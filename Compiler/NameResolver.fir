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
        let visitor = NameResolverVisitor(
            _tokens = module._tokens,
            _termEnv = ScopeMap.fromMap(module._termEnv),
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
    _tokens: Array[Token],
    _termEnv: ScopeMap[Str, VarDefIdx],
    _assocTermEnv: HashMap[Str, HashMap[Str, AssocVarDefIdx]],
    _tyEnv: HashMap[Str, TyDefIdx],
)


impl Visitor[NameResolverVisitor]:
    visitVarExpr(self: NameResolverVisitor, e: VarExpr):
        let varText = self._tokens.get(e.id.token.idx).text
        match self._termEnv.get(varText):
            Option.Some(idx): e.id.resolve(idx)
            Option.None: panic("Unbound variable `varText`")
