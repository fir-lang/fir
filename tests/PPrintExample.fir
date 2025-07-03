main():
    # Nested function calls, indented differently based on requested string width.
    let doc = makeCallSyntax(
        Doc.str("myFunction"),
        Vec.[
            Doc.str("longArgument1"),
            makeCallSyntax(
                Doc.str("myOtherFunction"),
                Vec.[
                    Doc.str("arg1"),
                    Doc.str("arg2"),
                ]),
            makeCallSyntax(Doc.str("yetAnotherFunction"), Vec.[]),
        ],
    )

    # Break at column 10: splits all groups into lines.
    print(doc.render(10))

    # Break at column 40: splits the outer group, but keeps the inner one flat.
    print(doc.render(40))

    # Break at column 100: prints the whole expression as one line.
    print(doc.render(100))

    print("")

    # Pretty printing combinators allow composing `Doc` values with multiple lines, without breaking
    # indentation and alignment.
    #
    # `expectationFailure` generates an error message. As arguments, we pass `Doc`s with multiple
    # lines and indentation. In the output, the second lines are indented the same amount relative
    # to the first lines.
    print(expectationFailure(
        Doc.nested(2, Doc.str("First user line") + Doc.hardLine() + Doc.str("indented 2")),
        Doc.nested(4, Doc.str("Second user line") + Doc.hardLine() + Doc.str("indented 4")),
    ).render(80))

makeCallSyntax(fun: Doc, args: Vec[Doc]) Doc:
    if args.len() == 0:
        return fun + Doc.str("()")

    let doc = fun + Doc.char('(') + Doc.break_(0)

    let numArgs = args.len()
    let argIdx = u32(0)
    for arg: Doc in args.iter():
        doc += arg
        if argIdx != numArgs - 1:
            doc += Doc.char(',')
            doc += Doc.break_(1)
        argIdx += 1

    # Add a trailing comma when splitting the arg list into lines.
    if args.len() != 0:
        doc += Doc.whenNotFlat(Doc.char(','))

    (doc.nest(4) + Doc.break_(0) + Doc.char(')')).group()

expectationFailure(expected: Doc, found: Doc) Doc:
    let expectedStr = "Expected: "
    let foundStr = "Found: "
    Doc.nested(expectedStr.len(), Doc.str(expectedStr) + expected)
        + Doc.hardLine()
        + Doc.nested(foundStr.len(), Doc.str(foundStr) + found)

# expected stdout:
# myFunction(
#     longArgument1,
#     myOtherFunction(
#         arg1,
#         arg2,
#     ),
#     yetAnotherFunction(),
# )
# myFunction(
#     longArgument1,
#     myOtherFunction(arg1, arg2),
#     yetAnotherFunction(),
# )
# myFunction(longArgument1, myOtherFunction(arg1, arg2), yetAnotherFunction())
# 
# Expected: First user line
#             indented 2
# Found: Second user line
#            indented 4
