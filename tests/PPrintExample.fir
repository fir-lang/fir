main
    let doc = \
        Doc.str("myFunction(") \
            .cat(Doc.break_(0)) \
            .cat(
                Doc.str("longArgument1")
                    .cat(Doc.char(','))
                    .cat(Doc.break_(1))
                    .cat(Doc.str("longArgument2"))
                    .cat(Doc.whenNotFlat(Doc.char(',')))
            ) \
            .nest(4) \
            .cat(Doc.break_(0)) \
            .cat(Doc.char(')')) \
            .group()

    print(doc.print(10))
    print(doc.print(100))

# expected stdout:
# myFunction(
#     longArgument1,
#     longArgument2,
# )
# myFunction(longArgument1, longArgument2)
