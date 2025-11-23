## Name resolving pass: loads modules, updates identifiers' to their definition
## indices.


import [
    Compiler/Ast,
    Compiler/AstVisitor,
    Compiler/Defs,
    Compiler/Module,
    Compiler/ScopeMap,
]


resolveNames(pgm: Program):
    _prepRenamingEnvs(pgm)

    for module: Module in pgm._modules.iter():
        let termEnv = ScopeMap.fromMap(module._termEnv)

        let visitor = _NameResolverVisitor(
            _moduleFilePath = module._filePath,
            _tokens = module._tokens,
            _termEnv = termEnv,
            _assocTermEnv = module._assocTermEnv,
            _tyEnv = module._tyEnv,
        )

        for funDecl: HashMapEntry[Str, FunDecl] in module._funItems.iter():
            let funDecl = funDecl.value
            visitor.visitFunDecl(funDecl)

        for tyDecl: HashMapEntry[Str, TypeDecl] in module._tyItems.iter():
            let tyDecl = tyDecl.value

            if tyDecl.rhs is Option.Some(rhs):
                match rhs:
                    TypeDeclRhs.Sum(cons):
                        for con: ConDecl in cons.iter():
                            visitor.visitConFields(con.fields)

                    TypeDeclRhs.Product(fields): visitor.visitConFields(fields)

        for traitDecl: HashMapEntry[Str, TraitDecl] in
                module._traitItems.iter():
            let traitDecl = traitDecl.value
            for funDecl: FunDecl in traitDecl.items.iter():
                visitor.visitFunDecl(funDecl)

        for implDecl: ImplDecl in module._impls.iter():
            for funDecl: FunDecl in implDecl.items.iter():
                visitor.visitFunDecl(funDecl)


type _NameResolverVisitor(
    _moduleFilePath: Str,
    _tokens: Array[Token],
    _termEnv: ScopeMap[Str, VarDefIdx],
    _assocTermEnv: HashMap[Str, HashMap[Str, AssocVarDefIdx]],
    _tyEnv: HashMap[Str, TyDefIdx],
)


impl Visitor[_NameResolverVisitor]:
    visitFunDecl(self: _NameResolverVisitor, funDecl: FunDecl):
        if funDecl.parentTy is Option.Some(id):
            self.visitTyId(id)

        self.visitFunSig(funDecl.sig)

        if funDecl.body is Option.Some(stmts):
            self._termEnv.enterScope()

            for param: FunArg in funDecl.sig.params.iter():
                let nameText = self._tokens.get(param.name.token.idx).text
                self._termEnv.insert(nameText, VarDefIdx.Local)

            for stmt: Stmt in stmts.iter():
                self.visitStmt(stmt)

            self._termEnv.exitScope()

        # BUG: #227.
        ()

    visitVarId(self: _NameResolverVisitor, id: VarId):
        let token = self._tokens.get(id.token.idx)
        let varText = token.text
        match self._termEnv.get(varText):
            Option.Some(idx): id.resolve(idx)
            Option.None:
                panic(
                    "`tokenLocStr(self._moduleFilePath, token)`: Unbound variable `varText`",
                )

    visitTyId(self: _NameResolverVisitor, id: TyId):
        let token = self._tokens.get(id.token.idx)
        let varText = token.text
        match self._tyEnv.get(varText):
            Option.Some(idx): id.resolve(idx)
            Option.None:
                panic(
                    "`tokenLocStr(self._moduleFilePath, token)`: Unbound type `varText`",
                )

    visitConstructor(self: _NameResolverVisitor, c: Constructor):
        if not c.variant:
            self.visitTyId(c.ty)
        for arg: Type in c.tyArgs.iter():
            self.visitType(arg)

    visitVarPat(self: _NameResolverVisitor, pat: VarPat):
        let varText = self._tokens.get(pat.var_.token.idx).text
        self._termEnv.insert(varText, VarDefIdx.Local)
        ()

    visitAlt(self: _NameResolverVisitor, alt: Alt):
        self._termEnv.enterScope()
        defaultVisitAlt(self, alt)
        self._termEnv.exitScope()
        ()

    visitLetStmt(self: _NameResolverVisitor, stmt: LetStmt):
        self.visitExpr(stmt.rhs)
        self.visitPat(stmt.lhs)

    visitForStmt(self: _NameResolverVisitor, stmt: ForStmt):
        self._termEnv.enterScope()

        # Visit iterator expression first as it cannot refer to loop binders.
        self.visitExpr(stmt.expr)

        # Bind loop binders.
        self.visitPat(stmt.pat)

        for stmt in stmt.body.iter():
            self.visitStmt(stmt)

        self._termEnv.exitScope()

        ()

    visitFnExpr(self: _NameResolverVisitor, fn_: FnExpr):
        self._termEnv.enterScope()

        for param: FunArg in fn_.sig.params.iter():
            let nameText = self._tokens.get(param.name.token.idx).text
            self._termEnv.insert(nameText, VarDefIdx.Local)

        for stmt: Stmt in fn_.body.iter():
            self.visitStmt(stmt)

        self._termEnv.exitScope()

        ()


tokenLocStr(filePath: Str, token: Token) Str:
    "`filePath`:`token.line + 1`:`token.col + 1`"


# ------------------------------------------------------------------------------
# Preparing name resolving environments


_prepRenamingEnvs(pgm: Program):
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
    let sccs = _sccs(pgm)
    pgm._depGraph = Option.Some(sccs)

    print("Program modules:")
    for i: U32 in range(u32(0), pgm._modules.len()):
        print("  `i`: `pgm._modules.get(i)._path`")

    print("Program SCCs:")
    print(sccs.toDoc().render(80))

    let sccEnvs: Vec[Option[_SccEnv]] = Vec.fromIter(
        repeatWith(||: Option.None).take(sccs.len()),
    )

    let sccImports = _makeSccDepGraph(pgm, sccs)
    print("SCC imports:")
    print(sccImports.toDoc().render(80))

    for sccIdx in range(u32(0), sccs.len()):
        _makeSccEnv(pgm, sccIdx, sccs, sccImports, sccEnvs)

    # Copy SCC envs to modules.
    for sccIdx: U32 in range(u32(0), sccs.len()):
        let sccEnv = sccEnvs.get(sccIdx).unwrap()
        let scc = sccs.get(sccIdx)
        for moduleIdx: ModuleIdx in scc.iter():
            let module = pgm._modules.get(moduleIdx._idx)

            # TODO: Module envs should be scope maps.
            module._termEnv = HashMap.fromEntries(sccEnv._termEnv.iter())
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


type _SccEnv(
    _termEnv: HashMap[Str, VarDefIdx],
    _assocTermEnv: HashMap[Str, HashMap[Str, AssocVarDefIdx]],
    _tyEnv: HashMap[Str, TyDefIdx],
)


_SccEnv.merge(self, other: _SccEnv):
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
    sccEnvs: Vec[Option[_SccEnv]],
) _SccEnv:
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

    let selfEnv = _SccEnv(
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
    let indexGen = _SccIndexGen(index = 0)

    # Because the module indices are consecutive numbers between 0 to number of
    # nodes, we use an `Array` to map module ids to things.
    let nodes: Array[_SccNode] = Array.fromIter(
        range(u32(0), pgm._modules.len()).map(
            |i: U32|:
                _SccNode(
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


type _SccNode(
    moduleIdx: ModuleIdx,
    index: Option[U32],
    lowLink: Option[U32],
    onStack: Bool,
)


type _SccIndexGen(
    index: U32,
)


_SccIndexGen.next(self) U32:
    let next = self.index
    self.index += 1
    next


_scc(
    pgm: Program,
    module: ModuleIdx,
    indexGen: _SccIndexGen,
    nodes: Array[_SccNode],
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
