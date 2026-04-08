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

import [Compiler/CompilerAst]


trait Visitor[v]:
    # ----------------------------------------------------------------
    # Declarations

    visitModule(self: v, d: Vec[CTopDecl]):
        defaultVisitModule(self, d)

    visitTopDecl(self: v, d: CTopDecl):
        defaultVisitTopDecl(self, d)

    visitTypeDecl(self: v, d: CTypeDecl):
        ()

    visitTypeDeclRhs(self: v, d: CTypeDeclRhs):
        ()

    visitConFields(self: v, d: CConFields):
        defaultVisitConFields(self, d)

    visitFunDecl(self: v, d: CFunDecl):
        ()

    visitImportDecl(self: v, d: CImportDecl):
        ()

    visitTraitDecl(self: v, d: CTraitDecl):
        ()

    visitImplDecl(self: v, d: CImplDecl):
        ()

    visitFunSig(self: v, d: CFunSig):
        defaultVisitFunSig(self, d)

    visitContext(self: v, d: CContext):
        defaultVisitContext(self, d)

    visitSelfParam(self: v, d: CSelfParam):
        ()

    visitFunArg(self: v, d: CFunArg):
        defaultVisitFunArg(self, d)

    # ----------------------------------------------------------------
    # Exprs

    visitExpr(self: v, e: CExpr):
        defaultVisitExpr(self, e)

    visitVarExpr(self: v, e: CVarExpr):
        defaultVisitVarExpr(self, e)

    visitConSelExpr(self: v, e: CCon):
        self.visitCon(e)

    visitFieldSelExpr(self: v, e: CFieldSelExpr):
        defaultVisitFieldSelExpr(self, e)

    visitAssocFnSelExpr(self: v, e: CAssocFnSelExpr):
        defaultVisitAssocFnSelExpr(self, e)

    visitCallExpr(self: v, e: CCallExpr):
        defaultVisitCallExpr(self, e)

    visitIntExpr(self: v, e: IntExpr):
        ()

    visitStrExpr(self: v, e: CStrExpr):
        ()

    visitCharExpr(self: v, e: CharExpr):
        ()

    visitBinOpExpr(self: v, e: CBinOpExpr):
        defaultVisitBinOp(self, e)

    visitUnOpExpr(self: v, e: CUnOpExpr):
        defaultVisitUnOp(self, e)

    visitRecordExpr(self: v, e: CRecordExpr):
        defaultVisitRecord(self, e)

    visitReturnExpr(self: v, e: CReturnExpr):
        defaultVisitReturn(self, e)

    visitMatchExpr(self: v, e: CMatchExpr):
        defaultVisitMatch(self, e)

    visitAlt(self: v, e: CAlt):
        defaultVisitAlt(self, e)

    visitIfExpr(self: v, e: CIfExpr):
        defaultVisitIf(self, e)

    visitFnExpr(self: v, e: CFnExpr):
        defaultVisitFn(self, e)

    visitIsExpr(self: v, e: CIsExpr):
        defaultVisitIs(self, e)

    visitDoExpr(self: v, e: CDoExpr):
        defaultVisitDo(self, e)

    visitSeqExpr(self: v, e: CSeqExpr):
        defaultVisitSeq(self, e)

    visitParenExpr(self: v, e: CParenExpr):
        defaultVisitParen(self, e)

    visitVariantExpr(self: v, e: CVariantExpr):
        defaultVisitVariant(self, e)

    # ----------------------------------------------------------------
    # Stmts

    visitStmt(self: v, e: CStmt):
        defaultVisitStmt(self, e)

    visitLetStmt(self: v, e: CLetStmt):
        defaultVisitLetStmt(self, e)

    visitAssignStmt(self: v, e: CAssignStmt):
        defaultVisitAssignStmt(self, e)

    visitExprStmt(self: v, e: CExpr):
        defaultVisitExprStmt(self, e)

    visitForStmt(self: v, e: CForStmt):
        defaultVisitForStmt(self, e)

    visitWhileStmt(self: v, e: CWhileStmt):
        defaultVisitWhileStmt(self, e)

    visitLoopStmt(self: v, e: CLoopStmt):
        defaultVisitLoopStmt(self, e)

    visitBreakStmt(self: v, e: BreakStmt):
        defaultVisitBreakStmt(self, e)

    visitContinueStmt(self: v, e: ContinueStmt):
        defaultVisitContinueStmt(self, e)

    # ----------------------------------------------------------------
    # Patterns

    visitPat(self: v, p: CPat):
        defaultVisitPat(self, p)

    visitVarPat(self: v, p: VarPat):
        ()

    visitConPat(self: v, p: CConPat):
        defaultVisitConPat(self, p)

    visitRecordPat(self: v, p: CRecordPat):
        defaultVisitRecordPat(self, p)

    visitIgnorePat(self: v, t: TokenIdx):
        ()

    visitStrPat(self: v, s: Str, t: TokenIdx):
        ()

    visitCharPat(self: v, c: Char, t: TokenIdx):
        ()

    visitOrPat(self: v, ps: Vec[CPat]):
        defaultVisitOrPat(self, ps)

    visitVariantPat(self: v, p: CVariantPat):
        defaultVisitVariantPat(self, p)

    # ----------------------------------------------------------------
    # Types

    visitType(self: v, t: CType):
        defaultVisitType(self, t)

    visitNamedType(self: v, t: CNamedType):
        defaultVisitNamedType(self, t)

    visitTypeVarType(self: v, t: Id):
        ()

    visitRecordType(self: v, t: CRecordType):
        defaultVisitRecordType(self, t)

    visitVariantType(self: v, t: CVariantType):
        defaultVisitVariantType(self, t)

    visitFnType(self: v, t: CFnType):
        defaultVisitFnType(self, t)

    visitAssocTySelectType(self: v, t: CAssocTySelectType):
        defaultVisitAssocTySelectType(self, t)

    visitTyArgs(self: v, t: CTyArgs):
        defaultVisitTyArgs(self, t)

    visitPred(self: v, p: CPred_):
        defaultVisitPred(self, p)

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

    visitCon(self: v, c: CCon):
        defaultVisitCon(self, c)


defaultVisitModule[Visitor[v]](v: v, module: Vec[CTopDecl]):
    for topDecl in module.iter():
        v.visitTopDecl(topDecl)


defaultVisitTopDecl[Visitor[v]](v: v, topDecl: CTopDecl):
    match topDecl:
        TopDecl.Type(d): v.visitTypeDecl(d)
        TopDecl.Fun(d): v.visitFunDecl(d)
        TopDecl.Import(d): v.visitImportDecl(d)
        TopDecl.Trait(d): v.visitTraitDecl(d)
        TopDecl.Impl(d): v.visitImplDecl(d)


defaultVisitFunSig[Visitor[v]](v: v, sig: CFunSig):
    if sig.context is Option.Some(context):
        v.visitContext(context)

    v.visitSelfParam(sig.self_)

    for param: CFunArg in sig.params.iter():
        v.visitFunArg(param)

    if sig.returnTy is Option.Some(ty):
        v.visitType(ty)

    if sig.exceptions is Option.Some(ty):
        v.visitType(ty)


defaultVisitFunArg[Visitor[v]](v: v, arg: CFunArg):
    if arg.ty is Option.Some(ty):
        v.visitType(ty)


defaultVisitContext[Visitor[v]](v: v, ctx: CContext):
    for pred: CPred_ in ctx.preds.iter():
        v.visitPred(pred)


defaultVisitConFields[Visitor[v]](v: v, fields: CConFields):
    match fields:
        ConFields.Empty: ()

        ConFields.Named(fields, ..):
            for field: CNamedField in fields.iter():
                v.visitType(field.ty)

        ConFields.Unnamed(fields):
            for ty: CType in fields.iter():
                v.visitType(ty)


defaultVisitExpr[Visitor[v]](v: v, expr: CExpr):
    match expr:
        Expr.Var(e): v.visitVarExpr(e)
        Expr.ConSel(e): v.visitConSelExpr(e)
        Expr.FieldSel(e): v.visitFieldSelExpr(e)
        Expr.AssocFnSel(e): v.visitAssocFnSelExpr(e)
        Expr.Call(e): v.visitCallExpr(e)
        Expr.Int(e): v.visitIntExpr(e)
        Expr.Str(e): v.visitStrExpr(e)
        Expr.Char(e): v.visitCharExpr(e)
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
        Expr.Variant(e): v.visitVariantExpr(e)


defaultVisitStmt[Visitor[v]](v: v, stmt: CStmt):
    match stmt:
        Stmt.Let(s): v.visitLetStmt(s)
        Stmt.Assign(s): v.visitAssignStmt(s)
        Stmt.Expr(s): v.visitExprStmt(s)
        Stmt.For(s): v.visitForStmt(s)
        Stmt.While(s): v.visitWhileStmt(s)
        Stmt.Loop(s): v.visitLoopStmt(s)
        Stmt.Break(s): v.visitBreakStmt(s)
        Stmt.Continue(s): v.visitContinueStmt(s)


defaultVisitPat[Visitor[v]](v: v, pat: CPat):
    match pat:
        Pat.Var(p): v.visitVarPat(p)
        Pat.Con(p): v.visitConPat(p)
        Pat.Record(p): v.visitRecordPat(p)
        Pat.Ignore(p): v.visitIgnorePat(p)
        Pat.Str(s, t): v.visitStrPat(s, t)
        Pat.Char(c, t): v.visitCharPat(c, t)
        Pat.Or(ps): v.visitOrPat(ps)
        Pat.Variant(p): v.visitVariantPat(p)


defaultVisitType[Visitor[v]](v: v, ty: CType):
    match ty:
        Type.Named(t): v.visitNamedType(t)
        Type.Var(t): v.visitTypeVarType(t)
        Type.Record(t): v.visitRecordType(t)
        Type.Variant(t): v.visitVariantType(t)
        Type.Fn_(t): v.visitFnType(t)
        Type.AssocTySelect(t): v.visitAssocTySelectType(t)


defaultVisitVarExpr[Visitor[v]](v: v, e: CVarExpr):
    v.visitVarId(e.id)
    if e.userTyArgs is Option.Some(args):
        v.visitTyArgs(args)


defaultVisitFieldSelExpr[Visitor[v]](v: v, e: CFieldSelExpr):
    # TODO: `field` field
    v.visitExpr(e.object)
    if e.userTyArgs is Option.Some(args):
        v.visitTyArgs(args)


defaultVisitAssocFnSelExpr[Visitor[v]](v: v, e: CAssocFnSelExpr):
    v.visitTyId(e.ty)
    v.visitAssocVarId(e.member)
    if e.userTyArgs is Option.Some(args):
        v.visitTyArgs(args)


defaultVisitCallExpr[Visitor[v]](v: v, e: CCallExpr):
    v.visitExpr(e.fun)
    for arg: Named[CExpr] in e.args.iter():
        v.visitExpr(arg.node)
    if e.splice is Option.Some(splice):
        v.visitExpr(splice)


defaultVisitBinOp[Visitor[v]](v: v, e: CBinOpExpr):
    v.visitExpr(e.left)
    v.visitExpr(e.right)


defaultVisitUnOp[Visitor[v]](v: v, e: CUnOpExpr):
    v.visitExpr(e.expr)


defaultVisitRecord[Visitor[v]](v: v, e: CRecordExpr):
    for field: Named[CExpr] in e.fields.iter():
        v.visitExpr(field.node)
    if e.splice is Option.Some(splice):
        v.visitExpr(splice)


defaultVisitReturn[Visitor[v]](v: v, e: CReturnExpr):
    if e.expr is Option.Some(e):
        v.visitExpr(e)


defaultVisitMatch[Visitor[v]](v: v, e: CMatchExpr):
    v.visitExpr(e.scrutinee)
    for alt: CAlt in e.alts.iter():
        v.visitAlt(alt)


defaultVisitAlt[Visitor[v]](v: v, e: CAlt):
    v.visitPat(e.pat)
    if e.guard is Option.Some(e):
        v.visitExpr(e)
    for stmt: CStmt in e.rhs.iter():
        v.visitStmt(stmt)


defaultVisitIf[Visitor[v]](v: v, e: CIfExpr):
    for branch: CIfBranch in e.branches.iter():
        v.visitExpr(branch.guard)
    if e.elseBranch is Option.Some(stmts):
        for stmt: CStmt in stmts.iter():
            v.visitStmt(stmt)


defaultVisitFn[Visitor[v]](v: v, e: CFnExpr):
    for stmt: CStmt in e.body.iter():
        v.visitStmt(stmt)


defaultVisitIs[Visitor[v]](v: v, e: CIsExpr):
    v.visitExpr(e.expr)
    v.visitPat(e.pat)


defaultVisitDo[Visitor[v]](v: v, e: CDoExpr):
    for stmt: CStmt in e.body.iter():
        v.visitStmt(stmt)


defaultVisitSeq[Visitor[v]](v: v, e: CSeqExpr):
    for elem: CSeqElem in e.elems.iter():
        if elem.key is Option.Some(e):
            v.visitExpr(e)
        v.visitExpr(elem.val)


defaultVisitParen[Visitor[v]](v: v, e: CParenExpr):
    v.visitExpr(e.expr)


defaultVisitVariant[Visitor[v]](v: v, e: CVariantExpr):
    v.visitExpr(e.expr)


defaultVisitCon[Visitor[v]](v: v, c: CCon):
    v.visitTyId(c.ty)
    if c.userTyArgs is Option.Some(args):
        v.visitTyArgs(args)


defaultVisitLetStmt[Visitor[v]](v: v, s: CLetStmt):
    v.visitPat(s.lhs)
    if s.ty is Option.Some(ty):
        v.visitType(ty)
    v.visitExpr(s.rhs)


defaultVisitAssignStmt[Visitor[v]](v: v, s: CAssignStmt):
    v.visitExpr(s.lhs)
    v.visitExpr(s.rhs)


defaultVisitExprStmt[Visitor[v]](v: v, s: CExpr):
    v.visitExpr(s)


defaultVisitForStmt[Visitor[v]](v: v, s: CForStmt):
    v.visitPat(s.pat)
    if s.astTy is Option.Some(ty):
        v.visitType(ty)
    v.visitExpr(s.expr)
    for stmt: CStmt in s.body.iter():
        v.visitStmt(stmt)


defaultVisitWhileStmt[Visitor[v]](v: v, s: CWhileStmt):
    v.visitExpr(s.cond)
    for stmt: CStmt in s.body.iter():
        v.visitStmt(stmt)


defaultVisitLoopStmt[Visitor[v]](v: v, s: CLoopStmt):
    for stmt: CStmt in s.body.iter():
        v.visitStmt(stmt)


defaultVisitBreakStmt[Visitor[v]](v: v, s: BreakStmt):
    ()


defaultVisitContinueStmt[Visitor[v]](v: v, s: ContinueStmt):
    ()


defaultVisitConPat[Visitor[v]](v: v, s: CConPat):
    v.visitCon(s.con)
    for field: Named[CPat] in s.fields.iter():
        v.visitPat(field.node)
    match s.rest:
        RestPat.Bind(varPat): v.visitVarPat(varPat)
        _: ()


defaultVisitRecordPat[Visitor[v]](v: v, s: CRecordPat):
    for field: Named[CPat] in s.fields.iter():
        v.visitPat(field.node)
    match s.rest:
        RestPat.Bind(varPat): v.visitVarPat(varPat)
        _: ()


defaultVisitOrPat[Visitor[v]](v: v, ps: Vec[CPat]):
    for p: CPat in ps.iter():
        v.visitPat(p)


defaultVisitVariantPat[Visitor[v]](v: v, p: CVariantPat):
    v.visitPat(p.pat)


defaultVisitNamedType[Visitor[v]](v: v, t: CNamedType):
    v.visitTyId(t.name)
    if t.args is Option.Some(args):
        v.visitTyArgs(args)


defaultVisitRecordType[Visitor[v]](v: v, t: CRecordType):
    for field: Named[CType] in t.fields.iter():
        v.visitType(field.node)
    if t.extension is Option.Some(ext):
        v.visitType(ext)


defaultVisitVariantType[Visitor[v]](v: v, t: CVariantType):
    for alt: CNamedType in t.alts.iter():
        v.visitNamedType(alt)
    if t.extension is Option.Some(ext):
        v.visitType(ext)


defaultVisitFnType[Visitor[v]](v: v, t: CFnType):
    for arg: CType in t.args.iter():
        v.visitType(arg)

    if t.ret is Option.Some(ret):
        v.visitType(ret)

    if t.exceptions is Option.Some(exn):
        v.visitType(exn)


defaultVisitAssocTySelectType[Visitor[v]](v: v, t: CAssocTySelectType):
    v.visitType(t.ty)


defaultVisitTyArgs[Visitor[v]](v: v, t: CTyArgs):
    for arg: CType in t.args.iter():
        v.visitType(arg)


defaultVisitPred[Visitor[v]](v: v, p: CPred_):
    match p:
        Pred_.Kind(name = _, kind):
            if kind is Option.Some(kind):
                v.visitType(kind)
        Pred_.App(app): v.visitNamedType(app)
        Pred_.AssocTyEq(ty, assocTy = _, eq):
            v.visitNamedType(ty)
            v.visitType(eq)
