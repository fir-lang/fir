import Ast

main():
    print("hi")


# --------------------------------------------------------------------------------------------------
# Expressions


Expr.format(self: Expr, tokens: Vec[Token]) Doc:
    match self:
        Expr.Var(e): e.format(tokens)
        Expr.ConstrSelect(e): e.format(tokens)
        Expr.FieldSelect(e): e.format(tokens)
        Expr.MethodSelect(e): e.format(tokens)
        Expr.AssocFnSelect(e): e.format(tokens)
        Expr.Call(e): e.format(tokens)
        Expr.Int(e): e.format(tokens)
        Expr.Str(e): e.format(tokens)
        Expr.Char(e): e.format(tokens)
        Expr.Self(e): Doc.str(tokenText(e, tokens))
        Expr.BinOp(e): e.format(tokens)
        Expr.UnOp(e): e.format(tokens)
        Expr.Record(e): e.format(tokens)
        Expr.Return(e): e.format(tokens)
        Expr.Match(e): e.format(tokens)
        Expr.If(e): e.format(tokens)
        Expr.Fn_(e): e.format(tokens)
        Expr.Is(e): e.format(tokens)
        Expr.Do(e): e.format(tokens)
        Expr.Seq(e): e.format(tokens)


VarExpr.format(self, tokens: Vec[Token]) Doc:
    Doc.str(idText(self.id, tokens)) + formatTyArgs(self.userTyArgs, tokens)


Constructor.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


FieldSelectExpr.format(self, tokens: Vec[Token]) Doc:
    #|
    Group sequence of selections so that we will format like one of the following:

        foo[T1].bar[t].baz[U32]

        foo[T1]
              .bar[t]
              .baz[U32]

    and not as:

        foo[T1]
              .bar[t]
                   .baz[U32]
    |#

    let selection = self
    let fields: Vec[(field: Id, tyArgs: Vec[Type])] = Vec.withCapacity(1)
    loop:
        fields.push((field = selection.field, tyArgs = selection.userTyArgs))
        if selection.object is Expr.FieldSelect(e):
            selection = e
        else:
            break

    let doc = selection.object.format(tokens)
    while fields.pop() is Option.Some((field, tyArgs)):
        doc += Doc.break_(0)
            + Doc.char('.')
            + Doc.str(idText(field, tokens))
            + formatTyArgs(tyArgs, tokens)

    doc.nest(4).group()


MethodSelectExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


AssocFnSelectExpr.format(self, tokens: Vec[Token]) Doc:
    Doc.nested(
        4,
        Doc.str(idText(self.ty, tokens))
            + Doc.break_(0)
            + Doc.char('.')
            + Doc.str(idText(self.member, tokens))
            + formatTyArgs(self.userTyArgs, tokens))
        .group()


CallExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


IntExpr.format(self, tokens: Vec[Token]) Doc:
    Doc.str(tokenText(self.token, tokens))


StrExpr.format(self, tokens: Vec[Token]) Doc:
    Doc.str(tokenText(self.token, tokens))


CharExpr.format(self, tokens: Vec[Token]) Doc:
    Doc.str(tokenText(self.token, tokens))


BinOpExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


UnOpExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


RecordExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


ReturnExpr.format(self, tokens: Vec[Token]) Doc:
    match self.expr:
        Option.None:
            Doc.str("return")

        Option.Some(expr):
            Doc.nested(
                4,
                Doc.str("return") + Doc.break_(1) + expr.format(tokens))
                .group()


MatchExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


IfExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


FnExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


IsExpr.format(self, tokens: Vec[Token]) Doc:
    Doc.nested(
        4,
        self.expr.format(tokens)
            + Doc.break_(1)
            + Doc.str("is ")
            + self.pat.format(tokens))
        .group()


DoExpr.format(self, tokens: Vec[Token]) Doc:
    let body = self.body.get(0).format(tokens)
    for stmt: Stmt in self.body.iter().skip(1):
        body += Doc.hardLine() + stmt.format(tokens)
    Doc.nested(4, Doc.str("do:") + Doc.hardLine() + body)


SeqExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


# --------------------------------------------------------------------------------------------------
# Statements


Stmt.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


# --------------------------------------------------------------------------------------------------
# Types


Type.format(self, tokens: Vec[Token]) Doc:
    match self:
        Type.Named(t): t.format(tokens)
        Type.Var(id): Doc.str(idText(id, tokens))
        Type.Record(t): t.format(tokens)
        Type.Variant(t): t.format(tokens)
        Type.Fn_(t): t.format(tokens)


NamedType.format(self, tokens: Vec[Token]) Doc:
    Doc.str(idText(self.name, tokens)) + formatTyArgs(self.args, tokens)


RecordType.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


VariantType.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


FnType.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


# --------------------------------------------------------------------------------------------------
# Patterns


Pat.format(self, tokens: Vec[Token]) Doc:
    match self:
        Pat.Var(p):
            p.format(tokens)

        Pat.Constr(p):
            p.format(tokens)

        Pat.Record(p):
            p.format(tokens)

        Pat.Ignore(p)
            | Pat.Str(_, p)
            | Pat.Char(_, p): Doc.str(tokenText(p, tokens))

        Pat.Or(p1, p2):
            Doc.nested(
                4,
                p1.format(tokens)
                    + Doc.break_(1)
                    + Doc.str("| ")
                    + p2.format(tokens))
                .group()


VarPat.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


ConstrPat.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


RecordPat.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


# --------------------------------------------------------------------------------------------------


formatTyArgs(tyArgs: Vec[Type], tokens: Vec[Token]) Doc:
    let doc = Doc.empty()

    if tyArgs.isEmpty():
        return doc

    doc += Doc.char('[')
    let i: U32 = 0
    for ty: Type in tyArgs.iter():
        if i != 0:
            doc += Doc.str(", ")
        doc += ty.format(tokens)
    doc += Doc.char(']')

    doc


idText(id: Id, tokens: Vec[Token]) Str:
    tokens.get(id.token.idx).text


tokenText(token: TokenIdx, tokens: Vec[Token]) Str:
    tokens.get(token.idx).text
