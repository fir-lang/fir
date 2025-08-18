main():
    let expr = joinBinOps(Vec.["blahh", "b", "c"])

    let stmt =
        Doc.nested(
            4,
            Doc.str("let")
                + Doc.blank(1)
                + Doc.str("foo")
                + Doc.blank(1)
                + Doc.char('=')
                + Doc.break_(1)
                + expr.group())

    print("Req: `stmt._req()`")
    print("")

    print(stmt.group().render(30))
    print("")
    print(stmt.group().render(20))
    print("")
    print(stmt.group().render(10))
    print("")
    print(
        Doc.flow(
            ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k"].map(Doc.str),
            Doc.char(',') + Doc.break_(1)
        )
        .render(10)
    )


joinBinOps(exprs: Vec[Str]) Doc:
    let doc = Doc.str(exprs.get(0))
    for expr: Str in exprs.iter().skip(1):
        doc += Doc.break_(1) + Doc.char('+') + Doc.blank(1) + Doc.str(expr)
    doc.nest(4)


commaSep(docs: Vec[Str]) Doc:
    if docs.isEmpty():
        return Doc.empty()

    let result = Doc.str(docs.get(0))
    for str: Str in docs.iter().skip(1):
        result = result + Doc.char(',') + Doc.break_(1) + Doc.str(str)

    result.group()
