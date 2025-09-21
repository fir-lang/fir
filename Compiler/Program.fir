## Defines the program-level state: package and module database.


import [
    Compiler/Ast,
    Compiler/Defs,
    Compiler/Error,
    Compiler/Grammar,
    Compiler/Scanner,
]


type Program(
    _modules: Vec[Module],
)


Program.new() Program:
    Program(_modules = Vec.empty())


## Load a module, or return it from the cache if it's already loaded.
##
## Follows imports in the module to transitively import all referred modules.
Program.loadCachedModule(self, path: Vec[Str]) ModuleIdx:
    for module: Module in self._modules.iter():
        if module._path == path:
            return module._idx

    print("Loading path: `path`...")

    let filePath = _modulePathToFilePath(path)
    let parsedModule = _parseFile(filePath)
    let moduleDecls = parsedModule.decls
    let tokens = parsedModule.tokens

    # Add the module to the program first to handle recursive imports.
    let moduleIdx = ModuleIdx(_idx = self._modules.len())

    let varItems: Vec[VarDef] = Vec.empty()
    let tyItems: Vec[TyDef] = Vec.empty()
    let traitItems: Vec[TraitDef] = Vec.empty()
    let impls: Vec[ImplDecl] = Vec.empty()
    let imports: Vec[Vec[Str]] = Vec.empty()
    for decl: TopDecl in moduleDecls.iter():
        match decl:
            TopDecl.Type(typeDecl):
                let idx = TyDefIdx_(_mod = moduleIdx, _tyIdx = tyItems.len())
                tyItems.push(TyDef(_ast = typeDecl, _idx = idx))

            TopDecl.Fun(funDecl):
                let idx = TopVarDefIdx(_mod = moduleIdx, _idx = varItems.len())
                varItems.push(VarDef(_ast = funDecl, _idx = idx))

            TopDecl.Trait(traitDecl):
                let idx = TraitDefIdx(
                    _mod = moduleIdx,
                    _traitIdx = traitItems.len(),
                )
                traitItems.push(TraitDef(_ast = traitDecl, _idx = idx))

            TopDecl.Impl(implDecl): impls.push(implDecl)

            TopDecl.Import(importDecl):
                for path: Vec[Id] in importDecl.paths.iter():
                    imports.push(
                        path.iter().map(
                            |id: Id| Str: tokens.get(id.token.idx).text,
                        ).toVec(),
                    )

    let module = Module(
        _package = _defaultPackage(),
        _path = path,
        _idx = moduleIdx,
        _varItems = varItems,
        _tyItems = tyItems,
        _traitItems = traitItems,
        _impls = impls,
        _imports = Vec.withCapacity(imports.len()),
        _tokens = tokens,
        _termEnv = HashMap.withCapacity(100),
        _tyEnv = HashMap.withCapacity(100),
        _sccIdx = Option.None,
    )

    self._modules.push(module)

    for import_: Vec[Str] in imports.iter():
        let importedModuleIdx = self.loadCachedModule(import_)
        module._imports.push(importedModuleIdx)

    moduleIdx


Program.prepModuleEnvs(self):
    # For now, the module system is simple to be compatible with the interpreter
    # and allow running the bootstrap compiler with the interpreter:
    #
    # - All module-level items are exported.
    # - Imports work as importing `*`, i.e. all exported items are imported and
    #   used directly with their names (no module prefix or renaming).
    #
    # That means each SCC has access to every top-level item in all of the nodes
    # in the SCC. So we create SCCs, and then create one module env for each
    # SCC, which is shared with all of the modules of the SCC.
    let sccs = _sccs(self)

    print("Program modules:")
    for i: U32 in range(u32(0), self._modules.len()):
        print("  `i`: `self._modules.get(i)._path`")

    print("Program SCCs:")
    print(sccs.toDoc().render(80))

    let sccs = _revTopSort(self, sccs)
    print("Program SCCs, sorted:")
    print(sccs.toDoc().render(80))


# ------------------------------------------------------------------------------
# Strongly connected components


## Find strongly connected components in the module dependency graph.
##
## The nodes in the dependency graph is `Program._modules`, and the edges are
## the imports in `Module._imports`.
##
## This implements Tarjan's SCC algorithm, as explained in Wikipedia.
_sccs(pgm: Program) Vec[HashSet[ModuleIdx]]:
    let indexGen = SccIndexGen(index = 0)

    # Because the module indices are consecutive numbers between 0 to number of
    # nodes, we use a `Vec` to map module ids to things.
    # TODO: We can't allocate an Array directly here because `RangeIterator`
    # doesn't implement `size`.
    let nodes: Array[SccNode] = Vec.fromIter(
        range(u32(0), pgm._modules.len()).map(
            |i: U32|:
                SccNode(
                    moduleIdx = ModuleIdx(_idx = i),
                    index = Option.None,
                    lowLink = Option.None,
                    onStack = Bool.False,
                ),
        ),
    ).takeArray()

    let output: Vec[HashSet[ModuleIdx]] = Vec.withCapacity(pgm._modules.len())

    let stack: Vec[ModuleIdx] = Vec.withCapacity(10)

    for module: Module in pgm._modules.iter():
        if nodes.get(module._idx._idx).index is Option.None:
            _scc(pgm, module._idx, indexGen, nodes, stack, output)

    output


type SccNode(
    moduleIdx: ModuleIdx,
    index: Option[U32],
    lowLink: Option[U32],
    onStack: Bool,
)


type SccIndexGen(
    index: U32,
)


SccIndexGen.next(self) U32:
    let next = self.index
    self.index += 1
    next


_scc(
    pgm: Program,
    module: ModuleIdx,
    indexGen: SccIndexGen,
    nodes: Array[SccNode],
    stack: Vec[ModuleIdx],
    output: Vec[HashSet[ModuleIdx]],
):
    let node = nodes.get(module._idx)
    let index = indexGen.next()
    node.index = Option.Some(index)
    node.lowLink = Option.Some(index)

    stack.push(module)
    node.onStack = Bool.True

    for depIdx: ModuleIdx in pgm._modules.get(module._idx)._imports.iter():
        let depNode = nodes.get(depIdx._idx)
        if depNode.index is Option.None:
            _scc(pgm, depNode.moduleIdx, indexGen, nodes, stack, output)
            node.lowLink = Option.Some(
                _minU32(node.lowLink.unwrap(), depNode.lowLink.unwrap()),
            )
        elif depNode.onStack:
            # Dep. is on stack, so in the current SCC.
            node.lowLink = Option.Some(
                _minU32(node.lowLink.unwrap(), depNode.index.unwrap()),
            )

    # If `node` is a root node, pop the stack and generate an SCC.
    if node.lowLink == node.index:
        let sccIdx = output.len()
        let scc: HashSet[ModuleIdx] = HashSet.withCapacity(5)
        loop:
            let dep = stack.pop().unwrap()
            let depNode = nodes.get(dep._idx)
            depNode.onStack = Bool.False
            scc.insert(dep)
            pgm._modules.get(dep._idx)._sccIdx = Option.Some(sccIdx)
            if dep == module:
                break
        output.push(scc)


# TODO: Implement this in the standard libs.
_minU32(i1: U32, i2: U32) U32:
    if i1 < i2:
        i1
    else:
        i2


# ------------------------------------------------------------------------------
# Topological sorting


## Reverse topological sort the strongly connected components.
##
## Reverse means child nodes (imported modules) will come before parents
## (importing modules) in the output.
_revTopSort(pgm: Program, sccs: Vec[HashSet[ModuleIdx]]) Vec[HashSet[ModuleIdx]]:
    # Generate imports from SCCs to other SCCs.
    let sccImports: Vec[HashSet[U32]] = Vec.withCapacity(sccs.len())

    # TODO: Add `repeatWith` in the standard libs.
    for i: U32 in range(u32(0), sccs.len()):
        sccImports.push(HashSet.withCapacity(10))

    for sccIdx: U32 in range(u32(0), sccs.len()):
        let importedSccs = sccImports.get(sccIdx)
        for mod: ModuleIdx in sccs.get(sccIdx).iter():
            for import_: ModuleIdx in
                    pgm._modules.get(mod._idx)._imports.iter():
                let importScc = pgm._modules.get(import_._idx)._sccIdx.unwrap()
                if importScc != sccIdx:
                    importedSccs.insert(importScc)

    # The dependency graph with `sccs` as the nodes and `sccImports` as the
    # edges don't have cycles, so we can depth-first traverse it, add child
    # nodes before parents to rev top sort.
    let output: Vec[HashSet[ModuleIdx]] = Vec.withCapacity(sccImports.len())

    # Find the root of the tree. This part is a bit hacky: we assume that
    # `ModuleIdx(0)` is the entry point, which can potentially change as we
    # refactor the code.
    # TODO: Add `Iterator.find` or similar.
    let rootSccIdx: Option[U32] = Option.None
    let rootModuleIdx = ModuleIdx(_idx = 0)
    for i: U32 in range(u32(0), sccs.len()):
        if sccs.get(i).contains(rootModuleIdx):
            rootSccIdx = Option.Some(i)
            break
    let rootSccIdx = rootSccIdx.unwrap()

    _dft(rootSccIdx, sccs, sccImports, output, HashSet.withCapacity(sccs.len()))

    output


_dft(
    sccIdx: U32,
    sccs: Vec[HashSet[ModuleIdx]],
    sccImports: Vec[HashSet[U32]],
    output: Vec[HashSet[ModuleIdx]],
    added: HashSet[U32],
):
    if added.contains(sccIdx):
        return

    added.insert(sccIdx)

    let currentScc = sccs.get(sccIdx)
    let currentSccImports = sccImports.get(sccIdx)

    # Add imports before the current SCC.
    for import_: U32 in currentSccImports.iter():
        _dft(import_, sccs, sccImports, output, added)

    output.push(sccs.get(sccIdx))


# ------------------------------------------------------------------------------


_parseFile(path: Str) (decls: Vec[TopDecl], tokens: Array[Token]):
    let fileContents = readFileUtf8(path)

    let (tokens, error) = tokenize(path, fileContents)
    if error is Option.Some(error):
        panic("`path`:`error.loc.line + 1`:`error.loc.col + 1`: `error.msg`")

    # Explicitly close the variant with `row[]`. (#49)
    let tokens = match try(||: scan[row[]](tokens)):
        Result.Err(~ScannerError(line, col, msg)):
            panic("`path`:`line + 1`:`col + 1`: `msg`")
        Result.Ok(tokens): tokens

    match try(||: module(ParserState.new(tokens))):
        Result.Err(cursor):
            match tokens.getOpt(cursor):
                Option.None: panic("`path`: unexpected end of input")
                Option.Some(token):
                    panic(
                        "`path`:`token.line + 1`:`token.col + 1`: unexpected token `token`",
                    )
        Result.Ok(mod): (decls = mod, tokens = tokens.takeArray())


_modulePathToFilePath(path: Vec[Str]) Str:
    let filePath = StrBuf.withCapacity(80)

    for i: U32 in range(u32(0), path.len()):
        if i != 0:
            filePath.push('/')
        filePath.pushStr(path.get(i))
        i += 1

    filePath.pushStr(".fir")
    filePath.toStr()


_defaultPackage() PackageUri:
    PackageUri(_uri = "pgk:default")
