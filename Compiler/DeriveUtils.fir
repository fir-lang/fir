import [
    Compiler/Ast,
    Compiler/Token,
]


checkPragma(expected: Str, decl: TypeDecl, tokens: Array[Token]) Bool:
    let attr = match decl.attr:
        Option.Some(attr): attr.expr
        Option.None: return Bool.False

    let (f, args) = match attr:
        Expr.Call(CallExpr(fun = Expr.Var(VarExpr(id, ..)), args, ..)):
            (f = id, args = args)
        _: return Bool.False

    let fStr = tokens.get(f.token.idx).text

    if fStr != "derive":
        return Bool.False

    for arg: Named[Expr] in args.iter():
        if arg.name is Option.Some(_):
            continue

        if arg.node is Expr.ConSel(Con(ty, con = Option.None, ..))
                and tokens.get(ty.token.idx).text == expected:
            return Bool.True

    Bool.False
