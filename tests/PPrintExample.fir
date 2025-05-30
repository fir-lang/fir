main()
    let args: Vec[Doc] = Vec.withCapacity(10)
    args.push(Doc.str("longArgument1"))

    let nestedCallArgs: Vec[Doc] = Vec.withCapacity(10)
    nestedCallArgs.push(Doc.str("arg1"))
    nestedCallArgs.push(Doc.str("arg2"))
    args.push(call(Doc.str("myOtherFunction"), nestedCallArgs))

    let nestedCallArgs: Vec[Doc] = Vec.withCapacity(10)
    args.push(call(Doc.str("yetAnotherFunction"), nestedCallArgs))

    let doc = call(Doc.str("myFunction"), args)

    # Break at column 10: splits all groups into lines.
    print(doc.print(10))

    # Break at column 40: splits the outer group, but keeps the inner one flat.
    print(doc.print(40))

    # Break at column 100: prints the whole expression as one line.
    print(doc.print(100))

call(fun: Doc, args: Vec[Doc]): Doc
    if args.len() == 0:
        return fun + Doc.str("()")

    let doc = fun + Doc.char('(') + Doc.break_(0)

    let numArgs = args.len()
    let argIdx = 0u32
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
