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
    for module: Module in pgm._modules.iter():
        let termEnv = ScopeMap.fromMap(module._termEnv)

        let visitor = NameResolverVisitor(
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


type NameResolverVisitor(
    _moduleFilePath: Str,
    _tokens: Array[Token],
    _termEnv: ScopeMap[Str, VarDefIdx],
    _assocTermEnv: HashMap[Str, HashMap[Str, AssocVarDefIdx]],
    _tyEnv: HashMap[Str, TyDefIdx],
)


impl Visitor[NameResolverVisitor]:
    visitFunDecl(self: NameResolverVisitor, funDecl: FunDecl):
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

    visitVarId(self: NameResolverVisitor, id: VarId):
        let token = self._tokens.get(id.token.idx)
        let varText = token.text
        match self._termEnv.get(varText):
            Option.Some(idx): id.resolve(idx)
            Option.None:
                panic(
                    "`tokenLocStr(self._moduleFilePath, token)`: Unbound variable `varText`",
                )

    visitTyId(self: NameResolverVisitor, id: TyId):
        let token = self._tokens.get(id.token.idx)
        let varText = token.text
        match self._tyEnv.get(varText):
            Option.Some(idx): id.resolve(idx)
            Option.None:
                panic(
                    "`tokenLocStr(self._moduleFilePath, token)`: Unbound type `varText`",
                )

    visitConstructor(self: NameResolverVisitor, c: Constructor):
        if not c.variant:
            self.visitTyId(c.ty)
        for arg: Type in c.tyArgs.iter():
            self.visitType(arg)

    visitVarPat(self: NameResolverVisitor, pat: VarPat):
        let varText = self._tokens.get(pat.var_.token.idx).text
        self._termEnv.insert(varText, VarDefIdx.Local)
        ()

    visitAlt(self: NameResolverVisitor, alt: Alt):
        self._termEnv.enterScope()
        defaultVisitAlt(self, alt)
        self._termEnv.exitScope()
        ()

    visitLetStmt(self: NameResolverVisitor, stmt: LetStmt):
        self.visitExpr(stmt.rhs)
        self.visitPat(stmt.lhs)

    visitForStmt(self: NameResolverVisitor, stmt: ForStmt):
        self._termEnv.enterScope()

        # Visit iterator expression first as it cannot refer to loop binders.
        self.visitExpr(stmt.expr)

        # Bind loop binders.
        self.visitPat(stmt.pat)

        for stmt in stmt.body.iter():
            self.visitStmt(stmt)

        self._termEnv.exitScope()

        ()

    visitFnExpr(self: NameResolverVisitor, fn_: FnExpr):
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
