## Name resolving pass: loads modules, updates identifiers' to their definition
## indices.


import [
    Compiler/Ast,
    Compiler/AstWalker,
    Compiler/Defs,
    Compiler/Error,
    Compiler/ScopeMap,
]


resolveNames(pgm: Program):
    for module: Module in pgm._modules.iter():
        let termEnv = ScopeMap.fromMap(module._termEnv)

        # Create a new scope to avoid modifying the module env with function
        # locals.
        termEnv.enterScope()

        let visitor = NameResolverVisitor(
            _moduleFilePath = module._filePath,
            _tokens = module._tokens,
            _termEnv = termEnv,
            _assocTermEnv = module._assocTermEnv,
            _tyEnv = module._tyEnv,
        )

        for funDecl: HashMapEntry[Str, FunDecl] in module._funItems.iter():
            let funDecl = funDecl.value
            if funDecl.body is Option.Some(stmts):
                for stmt: Stmt in stmts.iter():
                    walkStmt(stmt, visitor)

        ()


type NameResolverVisitor(
    _moduleFilePath: Str,
    _tokens: Array[Token],
    _termEnv: ScopeMap[Str, VarDefIdx],
    _assocTermEnv: HashMap[Str, HashMap[Str, AssocVarDefIdx]],
    _tyEnv: HashMap[Str, TyDefIdx],
)


impl Visitor[NameResolverVisitor]:
    visitVarExpr(self: NameResolverVisitor, e: VarExpr):
        let token = self._tokens.get(e.id.token.idx)
        let varText = token.text
        match self._termEnv.get(varText):
            Option.Some(idx): e.id.resolve(idx)
            Option.None:
                panic(
                    "`tokenLocStr(self._moduleFilePath, token)`: Unbound variable `varText`",
                )

    visitForStmt(self: NameResolverVisitor, e: ForStmt):
        self._termEnv.enterScope()

        # Visit iterator expression first as it cannot refer to loop binders.
        walkExpr(e.expr, self)

        # Bind loop binders.
        walkPat(e.pat, self)

        for stmt in e.body.iter():
            walkStmt(stmt, self)

        self._termEnv.exitScope()

        ()


tokenLocStr(filePath: Str, token: Token) Str:
    "`filePath`:`token.line + 1`:`token.col + 1`"
