## Defines the program-level state: package and module database.


import [
    Compiler/Ast,
    Compiler/Defs,
    Compiler/Error,
    Compiler/Grammar,
    Compiler/Module,
    Compiler/Scanner,
    Compiler/TypeCheck,
]


type Program(
    ## Indexed by `ModuleIdx`.
    _modules: Vec[Module],

    ## Strongly connected graphs of modules. Indexed by SCC indices.
    ##
    ## Initialized by `prepModuleEnvs`.
    _depGraph: Option[Vec[HashSet[ModuleIdx]]],
)


Program.new() Program:
    Program(_modules = Vec.empty(), _depGraph = Option.None,)


## Load a module, or return it from the cache if it's already loaded.
##
## Follows imports in the module to transitively import all referred modules.
Program.loadCachedModule(self, path: Vec[Str]) ModuleIdx:
    let firPreludePath = Vec.["Fir", "Prelude"]

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

    let funItems: HashMap[Str, FunDecl] = HashMap.withCapacity(100)
    let assocItems: HashMap[Str, HashMap[Str, FunDecl]] = HashMap.withCapacity(
        10,
    )
    let tyItems: HashMap[Str, TypeDecl] = HashMap.withCapacity(100)
    let traitItems: HashMap[Str, TraitDecl] = HashMap.withCapacity(10)
    let impls: Vec[ImplDecl] = Vec.empty()
    let imports: Vec[Vec[Str]] = Vec.empty()

    # Implicitly import `Fir/Prelude` in all modules.
    # TODO: Implement flag `--no-prelude`.
    # TODO: What happens if the module explicitly imports `Fir/Prelude`?
    if path != firPreludePath:
        imports.push(Vec.["Fir", "Prelude"])

    for decl: TopDecl in moduleDecls.iter():
        match decl:
            TopDecl.Type(typeDecl):
                let name = tokens.get(typeDecl.name.token.idx).text
                let old = tyItems.insert(name, typeDecl)
                if old is Option.Some(_):
                    panic("Type `name` defined multiple times in `filePath`")

            TopDecl.Fun(funDecl):
                match funDecl.parentTy:
                    Option.Some(parentTy):
                        let parentTyName = tokens.get(parentTy.token.idx).text
                        let assocFunMap = match assocItems.get(parentTyName):
                            Option.None:
                                let map = HashMap.withCapacity(10)
                                assocItems.insert(parentTyName, map)
                                map
                            Option.Some(map): map
                        let funName = tokens.get(funDecl.name.token.idx).text
                        let old = assocFunMap.insert(funName, funDecl)
                        if old is Option.Some(_):
                            panic(
                                "Associated function `parentTyName`.`funName` defined multipe times in `filePath`",
                            )

                    Option.None:
                        let funName = tokens.get(funDecl.name.token.idx).text
                        let old = funItems.insert(funName, funDecl)
                        if old is Option.Some(_):
                            panic(
                                "Function `funName` defined multipe times in `filePath`",
                            )

            TopDecl.Trait(traitDecl):
                let traitName = tokens.get(traitDecl.name.token.idx).text
                let old = traitItems.insert(traitName, traitDecl)
                if old is Option.Some(_):
                    panic(
                        "Trait `traitName` defined multiple times in `filePath`",
                    )

            TopDecl.Impl(implDecl): impls.push(implDecl)

            TopDecl.Import(importDecl):
                for path: Vec[Id] in importDecl.paths.iter():
                    imports.push(
                        Vec.fromIter(
                            path.iter().map(
                                |id: Id| Str: tokens.get(id.token.idx).text,
                            ),
                        ),
                    )

    let module = Module(
        _package = _defaultPackage(),
        _filePath = filePath,
        _path = path,
        _idx = moduleIdx,
        _funItems = funItems,
        _assocItems = assocItems,
        _tyItems = tyItems,
        _traitItems = traitItems,
        _impls = impls,
        _imports = Vec.withCapacity(imports.len()),
        _tokens = tokens,
        _termEnv = HashMap.withCapacity(100),
        _assocTermEnv = HashMap.withCapacity(10),
        _tyEnv = HashMap.withCapacity(100),
        _tcEnv = Option.None,
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
    #
    # - Imports work as importing `*`, i.e. all exported items are imported and
    #   used directly with their names (no module prefix or renaming).
    #
    # This means each SCC has access to every top-level item in all of the nodes
    # in the SCC. So we create SCCs, and then create one module env for each
    # SCC, which is shared with all of the modules of the SCC.
    let sccs = _sccs(self)
    self._depGraph = Option.Some(sccs)

    print("Program modules:")
    for i: U32 in range(u32(0), self._modules.len()):
        print("  `i`: `self._modules.get(i)._path`")

    print("Program SCCs:")
    print(sccs.toDoc().render(80))

    let sccEnvs: Vec[Option[SccEnv]] = Vec.fromIter(
        repeatWith(||: Option.None).take(sccs.len()),
    )

    let sccImports = _makeSccDepGraph(self, sccs)
    print("SCC imports:")
    print(sccImports.toDoc().render(80))

    for sccIdx in range(u32(0), sccs.len()):
        _makeSccEnv(self, sccIdx, sccs, sccImports, sccEnvs)

    # Copy SCC envs to modules.
    for sccIdx: U32 in range(u32(0), sccs.len()):
        let sccEnv = sccEnvs.get(sccIdx).unwrap()
        let scc = sccs.get(sccIdx)
        for moduleIdx: ModuleIdx in scc.iter():
            let module = self._modules.get(moduleIdx._idx)

            # TODO: Modul envs should be scope maps.
            module._termEnv = HashMap.fromIter(
                sccEnv._termEnv.iter().map(
                    |entry: HashMapEntry[Str, VarDefIdx]|:
                        (key = entry.key, value = entry.value),
                ),
            )

            module._assocTermEnv = sccEnv._assocTermEnv
            module._tyEnv = sccEnv._tyEnv


_makeSccDepGraph(pgm: Program, sccs: Vec[HashSet[ModuleIdx]]) Vec[HashSet[U32]]:
    let sccImports: Vec[HashSet[U32]] = Vec.fromIter(
        repeatWith(||: HashSet.withCapacity(10)).take(sccs.len()),
    )

    for sccIdx: U32 in range(u32(0), sccs.len()):
        let importedSccs = sccImports.get(sccIdx)
        for mod: ModuleIdx in sccs.get(sccIdx).iter():
            for import_: ModuleIdx in
                    pgm._modules.get(mod._idx)._imports.iter():
                let importScc = pgm._modules.get(import_._idx)._sccIdx.unwrap()
                if importScc != sccIdx:
                    importedSccs.insert(importScc)

    sccImports


type SccEnv(
    _termEnv: HashMap[Str, VarDefIdx],
    _assocTermEnv: HashMap[Str, HashMap[Str, AssocVarDefIdx]],
    _tyEnv: HashMap[Str, TyDefIdx],
)


SccEnv.merge(self, other: SccEnv):
    for term: HashMapEntry[Str, VarDefIdx] in other._termEnv.iter():
        let old = self._termEnv.insert(term.key, term.value)
        if old is Option.Some(oldImport) and oldImport != term.value:
            panic("Variable `term.key` defined multiple times in SCC")

    for assoc: HashMapEntry[Str, HashMap[Str, AssocVarDefIdx]] in
            other._assocTermEnv.iter():
        let termMap = match self._assocTermEnv.get(assoc.key):
            Option.Some(map): map
            Option.None:
                let map = HashMap.withCapacity(10)
                self._assocTermEnv.insert(assoc.key, map)
                map

        for term: HashMapEntry[Str, AssocVarDefIdx] in assoc.value.iter():
            let old = termMap.insert(term.key, term.value)
            if old is Option.Some(oldImport) and oldImport != term.value:
                panic(
                    "Associated function `assoc.key`.`term.key` defined multiple times in SCC",
                )

    for ty: HashMapEntry[Str, TyDefIdx] in other._tyEnv.iter():
        let old = self._tyEnv.insert(ty.key, ty.value)
        if old is Option.Some(oldImport) and oldImport != ty.value:
            panic("Type `ty.key` defined multiple times in SCC")


_makeSccEnv(
    pgm: Program,
    sccIdx: U32,
    sccs: Vec[HashSet[ModuleIdx]],
    sccImports: Vec[HashSet[U32]],
    sccEnvs: Vec[Option[SccEnv]],
) SccEnv:
    if sccEnvs.get(sccIdx) is Option.Some(env):
        return env

    let termEnv: HashMap[Str, VarDefIdx] = HashMap.withCapacity(50)
    let assocTermEnv: HashMap[Str, HashMap[Str, AssocVarDefIdx]] = HashMap
        .withCapacity(25)
    let typeEnv: HashMap[Str, TyDefIdx] = HashMap.withCapacity(25)

    let scc = sccs.get(sccIdx)

    for modIdx: ModuleIdx in scc.iter():
        let mod = pgm._modules.get(modIdx._idx)
        let tokens = mod._tokens

        for ty: HashMapEntry[Str, TypeDecl] in mod._tyItems.iter():
            let tyDefIdx = TyDefIdx(
                _mod = modIdx,
                _name = ty.key,
                _kind = TyDefKind.Type,
            )

            let old = typeEnv.insert(ty.key, tyDefIdx)
            if old is Option.Some(_):
                panic(
                    "Type `ty.key` defined multiple times in a recursive import group",
                )

        for trait_: HashMapEntry[Str, TraitDecl] in mod._traitItems.iter():
            let traitDefIdx = TyDefIdx(
                _mod = modIdx,
                _name = trait_.key,
                _kind = TyDefKind.Trait,
            )
            let old = typeEnv.insert(trait_.key, traitDefIdx)
            if old is Option.Some(_):
                panic(
                    "Type `trait_.key` defined multiple times in a recursive import group",
                )

        for fun: HashMapEntry[Str, FunDecl] in mod._funItems.iter():
            let varDefIdx = VarDefIdx.Top(
                TopVarDefIdx(_mod = modIdx, _name = fun.key),
            )
            let old = termEnv.insert(fun.key, varDefIdx)
            if old is Option.Some(_):
                panic(
                    "Value `fun.key` defined multiple times in a recursive import group",
                )

        for assocDef: HashMapEntry[Str, HashMap[Str, FunDecl]] in
                mod._assocItems.iter():
            let tyMap = match assocTermEnv.get(assocDef.key):
                Option.None:
                    let map = HashMap.withCapacity(10)
                    assocTermEnv.insert(assocDef.key, map)
                    map
                Option.Some(map): map

            for assocValue: HashMapEntry[Str, FunDecl] in assocDef.value.iter():
                let old = tyMap.insert(
                    assocValue.key,
                    AssocVarDefIdx(
                        _mod = modIdx,
                        _tyName = assocDef.key,
                        _varName = assocValue.key,
                    ),
                )
                if old is Option.Some(_):
                    panic(
                        "Value `assocDef.key`.`assocValue.key` defined multiple times in a recursive import group",
                    )

    let selfEnv = SccEnv(
        _termEnv = termEnv,
        _assocTermEnv = assocTermEnv,
        _tyEnv = typeEnv,
    )

    for importedSccIdx: U32 in sccImports.get(sccIdx).iter():
        let importedSccEnv = _makeSccEnv(
            pgm,
            importedSccIdx,
            sccs,
            sccImports,
            sccEnvs,
        )
        selfEnv.merge(importedSccEnv)

    sccEnvs.set(sccIdx, Option.Some(selfEnv))

    selfEnv


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
    # nodes, we use an `Array` to map module ids to things.
    let nodes: Array[SccNode] = Array.fromIter(
        range(u32(0), pgm._modules.len()).map(
            |i: U32|:
                SccNode(
                    moduleIdx = ModuleIdx(_idx = i),
                    index = Option.None,
                    lowLink = Option.None,
                    onStack = Bool.False,
                ),
        ),
        pgm._modules.len(),
    )

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
                min(node.lowLink.unwrap(), depNode.lowLink.unwrap()),
            )
        elif depNode.onStack:
            # Dep. is on stack, so in the current SCC.
            node.lowLink = Option.Some(
                min(node.lowLink.unwrap(), depNode.index.unwrap()),
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
