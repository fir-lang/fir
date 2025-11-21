#|
This module implements the AST `Visitor` trait with default implementations to
visit the fields, to make it convenient to traverse the ASTs.

Ideally, the default visit methods should visit all of the fields of AST nodes.
But that's too much work, so for now, we only visit the fields that we need to
visit in the use cases of the visitors. We should update the visitors and as we
need to visit more of the fields in new use sites.

In particular, for now, the top-level declaration visitors don't do anything.
Use sites should always override the top-level declaration visitors if they use
`visitModule`.
|#

import [Compiler/Ast]


trait Visitor[v]:
    # ----------------------------------------------------------------
    # Declarations

    visitModule(self: v, d: Vec[TopDecl]):
        defaultVisitModule(self, d)

    visitTopDecl(self: v, d: TopDecl):
        defaultVisitTopDecl(self, d)

    visitTypeDecl(self: v, d: TypeDecl):
        ()

    visitTypeDeclRhs(self: v, d: TypeDeclRhs):
        ()

    visitConFields(self: v, d: ConFields):
        defaultVisitConFields(self, d)

    visitFunDecl(self: v, d: FunDecl):
        ()

    visitImportDecl(self: v, d: ImportDecl):
        ()

    visitTraitDecl(self: v, d: TraitDecl):
        ()

    visitImplDecl(self: v, d: ImplDecl):
        ()

    visitFunSig(self: v, d: FunSig):
        defaultVisitFunSig(self, d)

    visitTypeParam(self: v, d: TypeParam):
        ()

    visitContext(self: v, d: Context):
        ()

    visitSelfParam(self: v, d: SelfParam):
        ()

    visitFunArg(self: v, d: FunArg):
        ()

    # ----------------------------------------------------------------
    # Exprs

    visitExpr(self: v, e: Expr):
        defaultVisitExpr(self, e)

    visitVarExpr(self: v, e: VarExpr):
        defaultVisitVarExpr(self, e)

    visitConstrSelectExpr(self: v, e: Constructor):
        self.visitConstructor(e)

    visitFieldSelectExpr(self: v, e: FieldSelectExpr):
        defaultVisitFieldSelectExpr(self, e)

    visitMethodSelectExpr(self: v, e: MethodSelectExpr):
        defaultVisitMethodSelectExpr(self, e)

    visitAssocFnSelectExpr(self: v, e: AssocFnSelectExpr):
        defaultVisitAssocFnSelectExpr(self, e)

    visitCallExpr(self: v, e: CallExpr):
        defaultVisitCallExpr(self, e)

    visitIntExpr(self: v, e: IntExpr):
        ()

    visitStrExpr(self: v, e: StrExpr):
        ()

    visitCharExpr(self: v, e: CharExpr):
        ()

    visitSelfExpr(self: v, e: TokenIdx):
        ()

    visitBinOpExpr(self: v, e: BinOpExpr):
        defaultVisitBinOp(self, e)

    visitUnOpExpr(self: v, e: UnOpExpr):
        defaultVisitUnOp(self, e)

    visitRecordExpr(self: v, e: RecordExpr):
        defaultVisitRecord(self, e)

    visitReturnExpr(self: v, e: ReturnExpr):
        defaultVisitReturn(self, e)

    visitMatchExpr(self: v, e: MatchExpr):
        defaultVisitMatch(self, e)

    visitAlt(self: v, e: Alt):
        defaultVisitAlt(self, e)

    visitIfExpr(self: v, e: IfExpr):
        defaultVisitIf(self, e)

    visitFnExpr(self: v, e: FnExpr):
        defaultVisitFn(self, e)

    visitIsExpr(self: v, e: IsExpr):
        defaultVisitIs(self, e)

    visitDoExpr(self: v, e: DoExpr):
        defaultVisitDo(self, e)

    visitSeqExpr(self: v, e: SeqExpr):
        defaultVisitSeq(self, e)

    visitParenExpr(self: v, e: ParenExpr):
        defaultVisitParen(self, e)

    # ----------------------------------------------------------------
    # Stmts

    visitStmt(self: v, e: Stmt):
        defaultVisitStmt(self, e)

    visitLetStmt(self: v, e: LetStmt):
        defaultVisitLetStmt(self, e)

    visitAssignStmt(self: v, e: AssignStmt):
        defaultVisitAssignStmt(self, e)

    visitExprStmt(self: v, e: Expr):
        defaultVisitExprStmt(self, e)

    visitForStmt(self: v, e: ForStmt):
        defaultVisitForStmt(self, e)

    visitWhileStmt(self: v, e: WhileStmt):
        defaultVisitWhileStmt(self, e)

    visitLoopStmt(self: v, e: LoopStmt):
        defaultVisitLoopStmt(self, e)

    visitBreakStmt(self: v, e: BreakStmt):
        defaultVisitBreakStmt(self, e)

    visitContinueStmt(self: v, e: ContinueStmt):
        defaultVisitContinueStmt(self, e)

    # ----------------------------------------------------------------
    # Patterns

    visitPat(self: v, p: Pat):
        defaultVisitPat(self, p)

    visitVarPat(self: v, p: VarPat):
        ()

    visitConstrPat(self: v, p: ConstrPat):
        defaultVisitConstrPat(self, p)

    visitRecordPat(self: v, p: RecordPat):
        defaultVisitRecordPat(self, p)

    visitIgnorePat(self: v, t: TokenIdx):
        ()

    visitStrPat(self: v, s: Str, t: TokenIdx):
        ()

    visitCharPat(self: v, c: Char, t: TokenIdx):
        ()

    visitOrPat(self: v, ps: Vec[Pat]):
        defaultVisitOrPat(self, ps)

    # ----------------------------------------------------------------
    # Types

    visitType(self: v, t: Type):
        defaultVisitType(self, t)

    visitNamedType(self: v, t: NamedType):
        defaultVisitNamedType(self, t)

    visitTypeVarType(self: v, t: Id):
        ()

    visitRecordType(self: v, t: RecordType):
        defaultVisitRecordType(self, t)

    visitVariantType(self: v, t: VariantType):
        defaultVisitVariantType(self, t)

    visitFnType(self: v, t: FnType):
        defaultVisitFnType(self, t)

    visitTyArgs(self: v, t: TyArgs):
        defaultVisitTyArgs(self, t)

    # ----------------------------------------------------------------
    # Ids

    visitVarId(self: v, id: VarId):
        ()

    visitTyId(self: v, id: TyId):
        ()

    visitAssocVarId(self: v, varId: AssocVarId):
        ()

    # ----------------------------------------------------------------
    # Shared things

    visitConstructor(self: v, c: Constructor):
        defaultVisitConstructor(self, c)


defaultVisitModule[Visitor[v]](v: v, module: Vec[TopDecl]):
    for topDecl in module.iter():
        v.visitTopDecl(topDecl)


defaultVisitTopDecl[Visitor[v]](v: v, topDecl: TopDecl):
    match topDecl:
        TopDecl.Type(d): v.visitTypeDecl(d)
        TopDecl.Fun(d): v.visitFunDecl(d)
        TopDecl.Import(d): v.visitImportDecl(d)
        TopDecl.Trait(d): v.visitTraitDecl(d)
        TopDecl.Impl(d): v.visitImplDecl(d)


defaultVisitFunSig[Visitor[v]](v: v, sig: FunSig):
    for typeParam: TypeParam in sig.typeParams.iter():
        v.visitTypeParam(typeParam)

    if sig.context is Option.Some(context):
        v.visitContext(context)

    v.visitSelfParam(sig.self_)

    for param: FunArg in sig.params.iter():
        v.visitFunArg(param)

    if sig.returnTy is Option.Some(ty):
        v.visitType(ty)

    if sig.exceptions is Option.Some(ty):
        v.visitType(ty)


defaultVisitConFields[Visitor[v]](v: v, fields: ConFields):
    match fields:
        ConFields.Empty: ()

        ConFields.Named(fields):
            for field: NamedField in fields.iter():
                v.visitType(field.ty)

        ConFields.Unnamed(fields):
            for ty: Type in fields.iter():
                v.visitType(ty)


defaultVisitExpr[Visitor[v]](v: v, expr: Expr):
    match expr:
        Expr.Var(e): v.visitVarExpr(e)
        Expr.ConstrSelect(e): v.visitConstrSelectExpr(e)
        Expr.FieldSelect(e): v.visitFieldSelectExpr(e)
        Expr.MethodSelect(e): v.visitMethodSelectExpr(e)
        Expr.AssocFnSelect(e): v.visitAssocFnSelectExpr(e)
        Expr.Call(e): v.visitCallExpr(e)
        Expr.Int(e): v.visitIntExpr(e)
        Expr.Str(e): v.visitStrExpr(e)
        Expr.Char(e): v.visitCharExpr(e)
        Expr.Self(e): v.visitSelfExpr(e)
        Expr.BinOp(e): v.visitBinOpExpr(e)
        Expr.UnOp(e): v.visitUnOpExpr(e)
        Expr.Record(e): v.visitRecordExpr(e)
        Expr.Return(e): v.visitReturnExpr(e)
        Expr.Match(e): v.visitMatchExpr(e)
        Expr.If(e): v.visitIfExpr(e)
        Expr.Fn_(e): v.visitFnExpr(e)
        Expr.Is(e): v.visitIsExpr(e)
        Expr.Do(e): v.visitDoExpr(e)
        Expr.Seq(e): v.visitSeqExpr(e)
        Expr.Paren(e): v.visitParenExpr(e)


defaultVisitStmt[Visitor[v]](v: v, stmt: Stmt):
    match stmt:
        Stmt.Let(s): v.visitLetStmt(s)
        Stmt.Assign(s): v.visitAssignStmt(s)
        Stmt.Expr(s): v.visitExprStmt(s)
        Stmt.For(s): v.visitForStmt(s)
        Stmt.While(s): v.visitWhileStmt(s)
        Stmt.Loop(s): v.visitLoopStmt(s)
        Stmt.Break(s): v.visitBreakStmt(s)
        Stmt.Continue(s): v.visitContinueStmt(s)


defaultVisitPat[Visitor[v]](v: v, pat: Pat):
    match pat:
        Pat.Var(p): v.visitVarPat(p)
        Pat.Constr(p): v.visitConstrPat(p)
        Pat.Record(p): v.visitRecordPat(p)
        Pat.Ignore(p): v.visitIgnorePat(p)
        Pat.Str(s, t): v.visitStrPat(s, t)
        Pat.Char(c, t): v.visitCharPat(c, t)
        Pat.Or(ps): v.visitOrPat(ps)


defaultVisitType[Visitor[v]](v: v, ty: Type):
    match ty:
        Type.Named(t): v.visitNamedType(t)
        Type.Var(t): v.visitTypeVarType(t)
        Type.Record(t): v.visitRecordType(t)
        Type.Variant(t): v.visitVariantType(t)
        Type.Fn_(t): v.visitFnType(t)


defaultVisitVarExpr[Visitor[v]](v: v, e: VarExpr):
    v.visitVarId(e.id)
    if e.userTyArgs is Option.Some(args):
        v.visitTyArgs(args)


defaultVisitFieldSelectExpr[Visitor[v]](v: v, e: FieldSelectExpr):
    # TODO: `field` field
    v.visitExpr(e.object)
    if e.userTyArgs is Option.Some(args):
        v.visitTyArgs(args)


defaultVisitMethodSelectExpr[Visitor[v]](v: v, e: MethodSelectExpr):
    v.visitExpr(e.object)
    v.visitTyId(e.methodTyId)
    v.visitAssocVarId(e.method)


defaultVisitAssocFnSelectExpr[Visitor[v]](v: v, e: AssocFnSelectExpr):
    v.visitTyId(e.ty)
    v.visitAssocVarId(e.member)
    if e.userTyArgs is Option.Some(args):
        v.visitTyArgs(args)


defaultVisitCallExpr[Visitor[v]](v: v, e: CallExpr):
    v.visitExpr(e.fun)
    for arg: Named[Expr] in e.args.iter():
        v.visitExpr(arg.node)


defaultVisitBinOp[Visitor[v]](v: v, e: BinOpExpr):
    v.visitExpr(e.left)
    v.visitExpr(e.right)


defaultVisitUnOp[Visitor[v]](v: v, e: UnOpExpr):
    v.visitExpr(e.expr)


defaultVisitRecord[Visitor[v]](v: v, e: RecordExpr):
    for field: Named[Expr] in e.fields.iter():
        v.visitExpr(field.node)


defaultVisitReturn[Visitor[v]](v: v, e: ReturnExpr):
    if e.expr is Option.Some(e):
        v.visitExpr(e)


defaultVisitMatch[Visitor[v]](v: v, e: MatchExpr):
    v.visitExpr(e.scrutinee)
    for alt: Alt in e.alts.iter():
        v.visitAlt(alt)


defaultVisitAlt[Visitor[v]](v: v, e: Alt):
    v.visitPat(e.pattern)
    if e.guard is Option.Some(e):
        v.visitExpr(e)
    for stmt: Stmt in e.rhs.iter():
        v.visitStmt(stmt)


defaultVisitIf[Visitor[v]](v: v, e: IfExpr):
    for branch: IfBranch in e.branches.iter():
        v.visitExpr(branch.guard)
    if e.elseBranch is Option.Some(stmts):
        for stmt: Stmt in stmts.iter():
            v.visitStmt(stmt)


defaultVisitFn[Visitor[v]](v: v, e: FnExpr):
    for stmt: Stmt in e.body.iter():
        v.visitStmt(stmt)


defaultVisitIs[Visitor[v]](v: v, e: IsExpr):
    v.visitExpr(e.expr)
    v.visitPat(e.pat)


defaultVisitDo[Visitor[v]](v: v, e: DoExpr):
    for stmt: Stmt in e.body.iter():
        v.visitStmt(stmt)


defaultVisitSeq[Visitor[v]](v: v, e: SeqExpr):
    for elem: SeqElem in e.elems.iter():
        if elem.key is Option.Some(e):
            v.visitExpr(e)
        v.visitExpr(elem.value)


defaultVisitParen[Visitor[v]](v: v, e: ParenExpr):
    v.visitExpr(e.expr)


defaultVisitConstructor[Visitor[v]](v: v, c: Constructor):
    v.visitTyId(c.ty)
    if c.userTyArgs is Option.Some(args):
        v.visitTyArgs(args)


defaultVisitLetStmt[Visitor[v]](v: v, s: LetStmt):
    v.visitPat(s.lhs)
    if s.ty is Option.Some(ty):
        v.visitType(ty)
    v.visitExpr(s.rhs)


defaultVisitAssignStmt[Visitor[v]](v: v, s: AssignStmt):
    v.visitExpr(s.lhs)
    v.visitExpr(s.rhs)


defaultVisitExprStmt[Visitor[v]](v: v, s: Expr):
    v.visitExpr(s)


defaultVisitForStmt[Visitor[v]](v: v, s: ForStmt):
    v.visitPat(s.pat)
    if s.astTy is Option.Some(ty):
        v.visitType(ty)
    v.visitExpr(s.expr)
    for stmt: Stmt in s.body.iter():
        v.visitStmt(stmt)


defaultVisitWhileStmt[Visitor[v]](v: v, s: WhileStmt):
    v.visitExpr(s.cond)
    for stmt: Stmt in s.body.iter():
        v.visitStmt(stmt)


defaultVisitLoopStmt[Visitor[v]](v: v, s: LoopStmt):
    for stmt: Stmt in s.body.iter():
        v.visitStmt(stmt)


defaultVisitBreakStmt[Visitor[v]](v: v, s: BreakStmt):
    ()


defaultVisitContinueStmt[Visitor[v]](v: v, s: ContinueStmt):
    ()


defaultVisitConstrPat[Visitor[v]](v: v, s: ConstrPat):
    v.visitConstructor(s.constr)
    for field: Named[Pat] in s.fields.iter():
        v.visitPat(field.node)


defaultVisitRecordPat[Visitor[v]](v: v, s: RecordPat):
    for field: Named[Pat] in s.fields.iter():
        v.visitPat(field.node)


defaultVisitOrPat[Visitor[v]](v: v, ps: Vec[Pat]):
    for p: Pat in ps.iter():
        v.visitPat(p)


defaultVisitNamedType[Visitor[v]](v: v, t: NamedType):
    v.visitTyId(t.name)
    if t.args is Option.Some(args):
        v.visitTyArgs(args)


defaultVisitRecordType[Visitor[v]](v: v, t: RecordType):
    for field: Named[Type] in t.fields.iter():
        v.visitType(field.node)


defaultVisitVariantType[Visitor[v]](v: v, t: VariantType):
    for alt: NamedType in t.alts.iter():
        v.visitNamedType(alt)


defaultVisitFnType[Visitor[v]](v: v, t: FnType):
    for arg: Type in t.args.iter():
        v.visitType(arg)

    if t.ret is Option.Some(ret):
        v.visitType(ret)

    if t.exceptions is Option.Some(exn):
        v.visitType(exn)


defaultVisitTyArgs[Visitor[v]](v: v, t: TyArgs):
    for arg: Type in t.args.iter():
        v.visitType(arg)
