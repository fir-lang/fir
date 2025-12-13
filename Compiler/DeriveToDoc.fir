import [
    Compiler/Assert,
    Compiler/Ast,
    Compiler/Grammar,
    Compiler/Lexer,
    Compiler/Scanner,
    Tool/Format/Format,
    Tool/Peg/PegTestLib,
]


deriveToDoc():
    let args = getArgs()

    if args.len() < 2:
        # TODO: print usage
        panic("Incorrect invocation of DeriveToDoc")

    let mode = args.get(1)
    match mode:
        "--test": test()
        "--file": genModule(readFileUtf8(args.get(2)))
        other: print("Unknown mode: `other`")


genModule(modStr: Str):
    let (tokens, error) = tokenize("<ToDoc module>", modStr)

    if error is Option.Some(error):
        panic(error.toStr())

    let tokens = match try(\(): scan[row[]](tokens)):
        Result.Err(~ScannerError(line, col, msg)):
            panic("Scanner error: `line + 1`:`col + 1`: `msg`")
        Result.Ok(tokens): tokens.takeArray()

    let parserState = ParserState.new(tokens)

    let tree = match try(\(): module(parserState)):
        Result.Err(err):
            panic("Unable to parse module: unexpected `tokens.get(err)`",)
        Result.Ok(tree): tree

    if not parserState.allConsumed():
        panic(
            "Parser didn't consume all input, input len = `tokens.len()`, cursor after parsing = `parserState._cursor`",
        )

    # print(genModule_(tree, tokens.takeArray()).render(80))
    print(formatModuleStr("test", genModule_(tree, tokens).render(80)),)


genModule_(module: Vec[TopDecl], tokens: Array[Token]) Doc:
    let doc = Doc.empty()

    for item: TopDecl in module.iter():
        if item is TopDecl.Type(decl):
            if checkPragma(typeDeclFirstToken(decl, tokens), tokens):
                doc += genItem(decl, tokens) + Doc.hardLine()

    doc


#|
type Foo[t](x: U32, y: t)

==>

impl[ToDoc[t]] ToDoc[Foo[t]]:
    toDoc(self: Foo[t]) Doc: ...
|#
genItem(item: TypeDecl, tokens: Array[Token]) Doc:
    assert(item.prim_ is Option.None)

    let head = Doc.str("impl")

    if not item.typeParams.isEmpty():
        head += Doc.char('[')

        let typeParamIdx: U32 = 0
        for typeParam: Id in item.typeParams.iter():
            if typeParamIdx != 0:
                head += Doc.str(", ")

            head += Doc.str("ToDoc[")
                + Doc.str(tokens.get(typeParam.token.idx).text)
                + Doc.char(']')

            typeParamIdx += 1

        head += Doc.char(']')

    let typeWithParams = typeWithParams(item.name, item.typeParams, tokens)

    head += Doc.blank(1) + Doc.str("ToDoc[") + typeWithParams + Doc.str("]:")

    let methodHead = Doc.str("toDoc(self: ")
        + typeWithParams
        + Doc.str(") Doc:")

    let methodBody = match item.rhs:
        Option.None: panic("Type doesn't have RHS")
        Option.Some(TypeDeclRhs.Sum(cons)): genSumBody(item.name, cons, tokens)
        Option.Some(TypeDeclRhs.Product(fields)):
            genProductBody(item.name, fields, tokens)

    head
        + Doc.nested(
            4,
            Doc.hardLine()
                + methodHead
                + Doc.nested(4, Doc.hardLine() + methodBody),
        )


typeWithParams(ty: Id, typeParams: Vec[Id], tokens: Array[Token]) Doc:
    let doc = Doc.str(tokens.get(ty.token.idx).text)

    if not typeParams.isEmpty():
        doc += Doc.char('[')

        let typeParamIdx: U32 = 0
        for typeParam: Id in typeParams.iter():
            if typeParamIdx != 0:
                doc += Doc.str(", ")

            doc += Doc.str(tokens.get(typeParam.token.idx).text)

            typeParamIdx += 1

        doc += Doc.char(']')

    doc


genSumBody(tyName: Id, cons: Vec[ConDecl], tokens: Array[Token]) Doc:
    let matchHead = Doc.str("match self:")

    let alts = Doc.empty()

    for con: ConDecl in cons.iter():
        let conNameStr = "`tokens.get(tyName.token.idx).text`.`tokens.get(con.name.token.idx).text`"

        let altHead = Doc.str(conNameStr)

        match con.fields:
            ConFields.Empty: ()

            ConFields.Named(namedFields):
                altHead += Doc.char('(')
                let fieldIdx: U32 = 0
                for field: NamedField in namedFields.iter():
                    if fieldIdx != 0:
                        altHead += Doc.str(", ")
                    altHead += Doc.str(tokens.get(field.name.token.idx).text)
                    fieldIdx += 1
                altHead += Doc.char(')')

            ConFields.Unnamed(unnamedFields):
                altHead += Doc.char('(')
                let fieldIdx: U32 = 0
                for ty: Type in unnamedFields.iter():
                    if fieldIdx != 0:
                        altHead += Doc.str(", ")
                    altHead += Doc.str("i`fieldIdx`")
                    fieldIdx += 1
                altHead += Doc.char(')')

        altHead += Doc.char(':')

        let altBody = Doc.empty()

        # Doc.str("Doc.str(`conNameStr`)")

        match con.fields:
            ConFields.Empty: altBody += Doc.str("Doc.str(\"`conNameStr`\")")

            ConFields.Named(namedFields):
                altBody += Doc.str("let args = Doc.break_(0)") + Doc.hardLine()

                let fieldIdx: U32 = 0
                for field: NamedField in namedFields.iter():
                    if fieldIdx != 0:
                        altBody += Doc.str(
                            "args += Doc.char(',') + Doc.break_(1)",
                        ) + Doc.hardLine()
                    let fieldNameStr = tokens.get(field.name.token.idx).text
                    altBody += Doc.str(
                        "args += Doc.grouped(Doc.str(\"`fieldNameStr` =\") + Doc.nested(4, Doc.break_(1) + `fieldNameStr`.toDoc()))",
                    ) + Doc.hardLine()
                    fieldIdx += 1

                altBody += Doc.str(
                    "args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')",
                ) + Doc.hardLine()

                altBody += Doc.str(
                    "Doc.str(\"`conNameStr`\") + Doc.char('(') + args",
                )

            ConFields.Unnamed(unnamedFields):
                altBody += Doc.str("let args = Doc.break_(0)") + Doc.hardLine()

                let fieldIdx: U32 = 0
                for ty: Type in unnamedFields.iter():
                    if fieldIdx != 0:
                        altBody += Doc.str(
                            "args += Doc.char(',') + Doc.break_(1)",
                        ) + Doc.hardLine()
                    altBody += Doc.str("args += i`fieldIdx`.toDoc()")
                        + Doc.hardLine()
                    fieldIdx += 1

                altBody += Doc.str(
                    "args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')",
                ) + Doc.hardLine()

                altBody += Doc.str(
                    "Doc.grouped(Doc.str(\"`conNameStr`\") + Doc.char('(') + args)",
                )

        alts += altHead
            + Doc.nested(4, Doc.hardLine() + altBody)
            + Doc.hardLine()

    matchHead + Doc.nested(4, Doc.hardLine() + alts)


genProductBody(ty: Id, fields: ConFields, tokens: Array[Token]) Doc:
    let doc = Doc.empty()

    match fields:
        ConFields.Empty: ()

        ConFields.Named(namedFields):
            doc += Doc.str("let args = Doc.break_(0)") + Doc.hardLine()

            let fieldIdx: U32 = 0
            for field: NamedField in namedFields.iter():
                if fieldIdx != 0:
                    doc += Doc.str("args += Doc.char(',') + Doc.break_(1)")
                        + Doc.hardLine()
                let fieldNameStr = tokens.get(field.name.token.idx).text
                doc += Doc.str(
                    "args += Doc.grouped(Doc.str(\"`fieldNameStr` =\") + Doc.nested(4, Doc.break_(1) + self.`fieldNameStr`.toDoc()))",
                ) + Doc.hardLine()
                fieldIdx += 1

            doc += Doc.str(
                "args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')",
            ) + Doc.hardLine()

        ConFields.Unnamed(unnamedFields): panic("TODO")

    doc
        + Doc.str(
            "Doc.grouped(Doc.str(\"`tokens.get(ty.token.idx).text`\") + Doc.char('(') + args)",
        )


checkPragma(token: TokenIdx, tokens: Array[Token]) Bool:
    if token.idx == 0:
        return Bool.False

    let prevIdx = token.idx - 1
    let prev = tokens.get(prevIdx)
    while prev.kind is TokenKind.Indent | TokenKind.Dedent | TokenKind.Newline
            and prevIdx != 0:
        prevIdx -= 1
        prev = tokens.get(prevIdx)

    prev.text == "#[derive(ToDoc)]"


typeDeclFirstToken(decl: TypeDecl, tokens: Array[Token]) TokenIdx:
    match decl.prim_:
        Option.Some(t): t
        Option.None: prevNonTrivia(decl.name.token, tokens).unwrap()


# --------------------------------------------------------------------------------------------------


test():
    genModule(
        "\
#[derive(ToDoc)]
type S1[t]:
    S1A
    S1B(t)
    S1C(t, U32)",
    )

    print("")

    genModule(
        "\
#[derive(ToDoc)]
type S2[t]:
    S2A
    S2B(x: t)
    S2C(x: t, y: U32)
    S2D(t)
    S2E(t, U32)",
    )

    print("")

    genModule("\
#[derive(ToDoc)]
type NamedType")

    print("")

    genModule("\
#[derive(ToDoc)]
type NamedType(name: Id)")

    print("")

    genModule(
        "\
#[derive(ToDoc)]
type NamedType(
    name: Id,
    args: Option[TyArgs],
)",
    )


# args after: --main deriveToDoc -- --test
# expected stdout:
# impl[ToDoc[t]] ToDoc[S1[t]]:
#     toDoc(self: S1[t]) Doc:
#         match self:
#             S1.S1A: Doc.str("S1.S1A")
#             S1.S1B(i0):
#                 let args = Doc.break_(0)
#                 args += i0.toDoc()
#                 args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
#                 Doc.grouped(Doc.str("S1.S1B") + Doc.char('(') + args)
#             S1.S1C(i0, i1):
#                 let args = Doc.break_(0)
#                 args += i0.toDoc()
#                 args += Doc.char(',') + Doc.break_(1)
#                 args += i1.toDoc()
#                 args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
#                 Doc.grouped(Doc.str("S1.S1C") + Doc.char('(') + args)
# 
# impl[ToDoc[t]] ToDoc[S2[t]]:
#     toDoc(self: S2[t]) Doc:
#         match self:
#             S2.S2A: Doc.str("S2.S2A")
#             S2.S2B(x):
#                 let args = Doc.break_(0)
#                 args += Doc.grouped(
#                     Doc.str("x =") + Doc.nested(4, Doc.break_(1) + x.toDoc()),
#                 )
#                 args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
#                 Doc.str("S2.S2B") + Doc.char('(') + args
#             S2.S2C(x, y):
#                 let args = Doc.break_(0)
#                 args += Doc.grouped(
#                     Doc.str("x =") + Doc.nested(4, Doc.break_(1) + x.toDoc()),
#                 )
#                 args += Doc.char(',') + Doc.break_(1)
#                 args += Doc.grouped(
#                     Doc.str("y =") + Doc.nested(4, Doc.break_(1) + y.toDoc()),
#                 )
#                 args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
#                 Doc.str("S2.S2C") + Doc.char('(') + args
#             S2.S2D(i0):
#                 let args = Doc.break_(0)
#                 args += i0.toDoc()
#                 args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
#                 Doc.grouped(Doc.str("S2.S2D") + Doc.char('(') + args)
#             S2.S2E(i0, i1):
#                 let args = Doc.break_(0)
#                 args += i0.toDoc()
#                 args += Doc.char(',') + Doc.break_(1)
#                 args += i1.toDoc()
#                 args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
#                 Doc.grouped(Doc.str("S2.S2E") + Doc.char('(') + args)
# 
# impl ToDoc[NamedType]:
#     toDoc(self: NamedType) Doc:
#         Doc.grouped(Doc.str("NamedType") + Doc.char('(') + args)
# 
# impl ToDoc[NamedType]:
#     toDoc(self: NamedType) Doc:
#         let args = Doc.break_(0)
#         args += Doc.grouped(
#             Doc.str("name =") + Doc.nested(4, Doc.break_(1) + self.name.toDoc()),
#         )
#         args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
#         Doc.grouped(Doc.str("NamedType") + Doc.char('(') + args)
# 
# impl ToDoc[NamedType]:
#     toDoc(self: NamedType) Doc:
#         let args = Doc.break_(0)
#         args += Doc.grouped(
#             Doc.str("name =") + Doc.nested(4, Doc.break_(1) + self.name.toDoc()),
#         )
#         args += Doc.char(',') + Doc.break_(1)
#         args += Doc.grouped(
#             Doc.str("args =") + Doc.nested(4, Doc.break_(1) + self.args.toDoc()),
#         )
#         args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
#         Doc.grouped(Doc.str("NamedType") + Doc.char('(') + args)
