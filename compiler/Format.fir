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
        Expr.Self(e): Doc.str(tokenText(tokens, e))
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
    panic("TODO")


MethodSelectExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


AssocFnSelectExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


CallExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


IntExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


StrExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


CharExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


BinOpExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


UnOpExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


RecordExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


ReturnExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


MatchExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


IfExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


FnExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


IsExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


DoExpr.format(self, tokens: Vec[Token]) Doc:
    panic("TODO")


SeqExpr.format(self, tokens: Vec[Token]) Doc:
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


tokenText(tokens: Vec[Token], token: TokenIdx) Str:
    tokens.get(token.idx).text
