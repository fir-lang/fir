import [Compiler/Ast]


walkExpr[Visitor[v]](expr: Expr, v: v):
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


walkStmt[Visitor[v]](stmt: Stmt, v: v):
    match stmt:
        Stmt.Let(s): v.visitLetStmt(s)
        Stmt.Assign(s): v.visitAssignStmt(s)
        Stmt.Expr(s): v.visitExprStmt(s)
        Stmt.For(s): v.visitForStmt(s)
        Stmt.While(s): v.visitWhileStmt(s)
        Stmt.Loop(s): v.visitLoopStmt(s)
        Stmt.Break(s): v.visitBreakStmt(s)
        Stmt.Continue(s): v.visitContinueStmt(s)


walkPat[Visitor[v]](pat: Pat, v: v):
    match pat:
        Pat.Var(p): v.visitVarPat(p)
        Pat.Constr(p): v.visitConstrPat(p)
        Pat.Record(p): v.visitRecordPat(p)
        Pat.Ignore(p): v.visitIgnorePat(p)
        Pat.Str(s, t): v.visitStrPat(s, t)
        Pat.Char(c, t): v.visitCharPat(c, t)
        Pat.Or(ps): v.visitOrPat(ps)


trait Visitor[t]:
    # ----------------------------------------------------------------
    # Exprs

    visitVarExpr(self: t, e: VarExpr):
        ()

    visitConstrSelectExpr(self: t, e: Constructor):
        ()

    visitFieldSelectExpr(self: t, e: FieldSelectExpr):
        defaultVisitFieldSelectExpr(self, e)

    visitMethodSelectExpr(self: t, e: MethodSelectExpr):
        defaultVisitMethodSelectExpr(self, e)

    visitAssocFnSelectExpr(self: t, e: AssocFnSelectExpr):
        ()

    visitCallExpr(self: t, e: CallExpr):
        defaultVisitCallExpr(self, e)

    visitIntExpr(self: t, e: IntExpr):
        ()

    visitStrExpr(self: t, e: StrExpr):
        ()

    visitCharExpr(self: t, e: CharExpr):
        ()

    visitSelfExpr(self: t, e: TokenIdx):
        ()

    visitBinOpExpr(self: t, e: BinOpExpr):
        defaultVisitBinOp(self, e)

    visitUnOpExpr(self: t, e: UnOpExpr):
        defaultVisitUnOp(self, e)

    visitRecordExpr(self: t, e: RecordExpr):
        defaultVisitRecord(self, e)

    visitReturnExpr(self: t, e: ReturnExpr):
        defaultVisitReturn(self, e)

    visitMatchExpr(self: t, e: MatchExpr):
        defaultVisitMatch(self, e)

    visitAlt(self: t, e: Alt):
        defaultVisitAlt(self, e)

    visitIfExpr(self: t, e: IfExpr):
        defaultVisitIf(self, e)

    visitFnExpr(self: t, e: FnExpr):
        defaultVisitFn(self, e)

    visitIsExpr(self: t, e: IsExpr):
        defaultVisitIs(self, e)

    visitDoExpr(self: t, e: DoExpr):
        defaultVisitDo(self, e)

    visitSeqExpr(self: t, e: SeqExpr):
        defaultVisitSeq(self, e)

    visitParenExpr(self: t, e: ParenExpr):
        defaultVisitParen(self, e)

    # ----------------------------------------------------------------
    # Stmts

    visitLetStmt(self: t, e: LetStmt):
        defaultVisitLetStmt(self, e)

    visitAssignStmt(self: t, e: AssignStmt):
        defaultVisitAssignStmt(self, e)

    visitExprStmt(self: t, e: Expr):
        defaultVisitExprStmt(self, e)

    visitForStmt(self: t, e: ForStmt):
        defaultVisitForStmt(self, e)

    visitWhileStmt(self: t, e: WhileStmt):
        defaultVisitWhileStmt(self, e)

    visitLoopStmt(self: t, e: LoopStmt):
        defaultVisitLoopStmt(self, e)

    visitBreakStmt(self: t, e: BreakStmt):
        defaultVisitBreakStmt(self, e)

    visitContinueStmt(self: t, e: ContinueStmt):
        defaultVisitContinueStmt(self, e)

    # ----------------------------------------------------------------
    # Pats

    visitVarPat(self: t, p: VarPat):
        ()

    visitConstrPat(self: t, p: ConstrPat):
        defaultVisitConstrPat(self, p)

    visitRecordPat(self: t, p: RecordPat):
        defaultVisitRecordPat(self, p)

    visitIgnorePat(self: t, t: TokenIdx):
        ()

    visitStrPat(self: t, s: Str, t: TokenIdx):
        ()

    visitCharPat(self: t, c: Char, t: TokenIdx):
        ()

    visitOrPat(self: t, ps: Vec[Pat]):
        defaultVisitOrPat(self, ps)


defaultVisitFieldSelectExpr[Visitor[t]](visitor: t, e: FieldSelectExpr):
    walkExpr(e.object, visitor)


defaultVisitMethodSelectExpr[Visitor[t]](visitor: t, e: MethodSelectExpr):
    walkExpr(e.object, visitor)


defaultVisitCallExpr[Visitor[t]](visitor: t, e: CallExpr):
    walkExpr(e.fun, visitor)
    for arg: Named[Expr] in e.args.iter():
        walkExpr(arg.node, visitor)


defaultVisitBinOp[Visitor[t]](visitor: t, e: BinOpExpr):
    walkExpr(e.left, visitor)
    walkExpr(e.right, visitor)


defaultVisitUnOp[Visitor[t]](visitor: t, e: UnOpExpr):
    walkExpr(e.expr, visitor)


defaultVisitRecord[Visitor[t]](visitor: t, e: RecordExpr):
    for field: Named[Expr] in e.fields.iter():
        walkExpr(field.node, visitor)


defaultVisitReturn[Visitor[t]](visitor: t, e: ReturnExpr):
    if e.expr is Option.Some(e):
        walkExpr(e, visitor)


defaultVisitMatch[Visitor[t]](visitor: t, e: MatchExpr):
    walkExpr(e.scrutinee, visitor)
    for alt: Alt in e.alts.iter():
        visitor.visitAlt(alt)


defaultVisitAlt[Visitor[t]](visitor: t, e: Alt):
    walkPat(e.pattern, visitor)
    if e.guard is Option.Some(e):
        walkExpr(e, visitor)
    for stmt: Stmt in e.rhs.iter():
        walkStmt(stmt, visitor)


defaultVisitIf[Visitor[t]](visitor: t, e: IfExpr):
    for branch: IfBranch in e.branches.iter():
        walkExpr(branch.guard, visitor)
    if e.elseBranch is Option.Some(stmts):
        for stmt: Stmt in stmts.iter():
            walkStmt(stmt, visitor)


defaultVisitFn[Visitor[t]](visitor: t, e: FnExpr):
    for stmt: Stmt in e.body.iter():
        walkStmt(stmt, visitor)


defaultVisitIs[Visitor[t]](visitor: t, e: IsExpr):
    walkExpr(e.expr, visitor)
    walkPat(e.pat, visitor)


defaultVisitDo[Visitor[t]](visitor: t, e: DoExpr):
    for stmt: Stmt in e.body.iter():
        walkStmt(stmt, visitor)


defaultVisitSeq[Visitor[t]](visitor: t, e: SeqExpr):
    for elem: SeqElem in e.elems.iter():
        if elem.key is Option.Some(e):
            walkExpr(e, visitor)
        walkExpr(elem.value, visitor)


defaultVisitParen[Visitor[t]](visitor: t, e: ParenExpr):
    walkExpr(e.expr, visitor)


defaultVisitLetStmt[Visitor[t]](visitor: t, s: LetStmt):
    walkPat(s.lhs, visitor)
    walkExpr(s.rhs, visitor)


defaultVisitAssignStmt[Visitor[t]](visitor: t, s: AssignStmt):
    walkExpr(s.lhs, visitor)
    walkExpr(s.rhs, visitor)


defaultVisitExprStmt[Visitor[t]](visitor: t, s: Expr):
    walkExpr(s, visitor)


defaultVisitForStmt[Visitor[t]](visitor: t, s: ForStmt):
    walkExpr(s.expr, visitor)
    for stmt: Stmt in s.body.iter():
        walkStmt(stmt, visitor)


defaultVisitWhileStmt[Visitor[t]](visitor: t, s: WhileStmt):
    walkExpr(s.cond, visitor)
    for stmt: Stmt in s.body.iter():
        walkStmt(stmt, visitor)


defaultVisitLoopStmt[Visitor[t]](visitor: t, s: LoopStmt):
    for stmt: Stmt in s.body.iter():
        walkStmt(stmt, visitor)


defaultVisitBreakStmt[Visitor[t]](visitor: t, s: BreakStmt):
    ()


defaultVisitContinueStmt[Visitor[t]](visitor: t, s: ContinueStmt):
    ()


defaultVisitConstrPat[Visitor[t]](visitor: t, s: ConstrPat):
    for field: Named[Pat] in s.fields.iter():
        walkPat(field.node, visitor)


defaultVisitRecordPat[Visitor[t]](visitor: t, s: RecordPat):
    for field: Named[Pat] in s.fields.iter():
        walkPat(field.node, visitor)


defaultVisitOrPat[Visitor[t]](visitor: t, ps: Vec[Pat]):
    for p: Pat in ps.iter():
        walkPat(p, visitor)
