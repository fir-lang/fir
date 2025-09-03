import Grammar
import Lexer
import Peg.PegTestLib
import Compiler.Scanner


main(args: Array[Str]):
    if args.len() < 2:
        # TODO: print usage
        panic("Incorrect invocation of DeriveEq")

    let mode = args.get(1)
    match mode:
        "--test": test()
        "--item": gen(args.get(2))
        "--file": gen(readFileUtf8(args.get(2)))
        other: print("Unknown mode: `other`")


gen(item: Str):
    let (tokens, error) = tokenize("<ToStr item>", item)

    if error is Option.Some(error):
        panic(error.toStr())

    tokens = match try(||: scan[row[]](tokens)):
        Result.Err(~ScannerError(line, col, msg)):
            panic("Scanner error: `line + 1`:`col + 1`: `msg`")
        Result.Ok(tokens): tokens

    let parserState = ParserState.new(tokens)

    let tree = match try(||: typeDecl(parserState)):
        Result.Err(err):
            panic(
                "Unable to parse item as type decl: unexpected `tokens.get(err)`",
            )
        Result.Ok(tree): tree

    if not parserState.allConsumed():
        panic(
            "Parser didn't consume all input, input len = `tokens.len()`, cursor after parsing = `parserState._cursor`",
        )

    print(genTree(tree, tokens).render(80))


genTree(typeDecl: TypeDecl, tokens: Vec[Token]) Doc:
    let typeName = tokens.get(typeDecl.name.token.idx).text

    let methodBody = match typeDecl.rhs:
        Option.None: Doc.empty()

        Option.Some(TypeDeclRhs.Sum(cons)): genSumAlts(typeName, cons, tokens)

        Option.Some(TypeDeclRhs.Product(fields)):
            genProduct(typeName, fields, tokens)

    let preds = Doc.empty()
    if typeDecl.typeParams.len() != 0:
        preds = _brackets(
            _interleave(
                typeDecl.typeParams,
                |param|:
                    Doc.str("Eq[")
                        + Doc.str(tokens.get(param.token.idx).text)
                        + Doc.char(']'),
                Doc.str(", "),
            ),
        )

    let typeParamsDoc = Doc.empty()
    if typeDecl.typeParams.len() != 0:
        typeParamsDoc = _brackets(
            _interleave(
                typeDecl.typeParams,
                |param|: Doc.str(tokens.get(param.token.idx).text),
                Doc.str(", "),
            ),
        )

    let typeNameDoc = Doc.str(typeName)

    Doc.nested(
        4,
        Doc.str("impl")
            + preds
            + Doc.str(" Eq[")
            + typeNameDoc
            + typeParamsDoc
            + Doc.str("]:")
            + Doc.hardLine()
            + Doc.nested(
                4,
                Doc.str("__eq(self: ")
                    + typeNameDoc
                    + typeParamsDoc
                    + Doc.str(", other: ")
                    + typeNameDoc
                    + typeParamsDoc
                    + Doc.str(") Bool:")
                    + Doc.hardLine()
                    + methodBody,
            ),
    )


genSumAlts(typeName: Str, decls: Vec[ConDecl], tokens: Vec[Token]) Doc:
    let alts = Doc.empty()
    let i = u32(0)
    for conDecl: ConDecl in decls.iter():
        if i != 0:
            alts += Doc.hardLine()
        i += 1
        let l = genConPat('l', typeName, conDecl, tokens)
        let r = genConPat('r', typeName, conDecl, tokens)
        let pat = makeLRRecord(l, r)
        alts += Doc.nested(
            4,
            pat + Doc.char(':') + Doc.hardLine() + genSumRhs(typeName, conDecl),
        )
    Doc.nested(
        4,
        Doc.str("match (l = self, r = other):") + Doc.hardLine() + alts,
    )


genConPat(varPrefix: Char, typeName: Str, conDecl: ConDecl, tokens: Vec[Token]) Doc:
    let fieldPats = match conDecl.fields:
        ConFields.Empty:
            return Doc.str(typeName)
                + Doc.char('.')
                + Doc.str(tokens.get(conDecl.name.token.idx).text)

        ConFields.Named(fields): genNamedFieldPats(varPrefix, fields, tokens)

        ConFields.Unnamed(fields): genUnnamedFieldPats(varPrefix, fields)

    Doc.str(typeName)
        + Doc.char('.')
        + Doc.str(tokens.get(conDecl.name.token.idx).text)
        + Doc.char('(')
        + fieldPats
        + Doc.char(')')


genNamedFieldPats(
    varPrefix: Char,
    fields: Vec[(name: Id, ty: Type)],
    tokens: Vec[Token],
) Doc:
    let doc = Doc.empty()
    for i: U32 in range(u32(0), fields.len()):
        if i != 0:
            doc += Doc.str(", ")
        doc += Doc.str(tokens.get(fields.get(i).name.token.idx).text)
            + Doc.str(" = ")
            + Doc.char(varPrefix)
            + Doc.str(i.toStr())
    doc


genUnnamedFieldPats(varPrefix: Char, fields: Vec[Type]) Doc:
    let doc = Doc.empty()
    for i: U32 in range(u32(0), fields.len()):
        if i != 0:
            doc += Doc.str(", ")
        doc += Doc.char(varPrefix) + Doc.str(i.toStr())
    doc


genUnnamedFieldsBody(conName: Doc, numFields: U32) Doc:
    let doc = conName + Doc.char('(')
    for i: U32 in range(u32(0), numFields):
        if i != 0:
            doc += Doc.str(", ")
        doc += Doc.char('x') + Doc.str(i.toStr())
    doc + Doc.char(')')


genSumRhs(typeName: Str, conDecl: ConDecl) Doc:
    let numFields = match conDecl.fields:
        ConFields.Empty: return Doc.str("Bool.True")

        ConFields.Named(fields): fields.len()

        ConFields.Unnamed(fields): fields.len()

    let rhs = Doc.empty()

    for i: U32 in range(u32(0), numFields):
        if i != 0:
            rhs += Doc.str(" && ")
        rhs += Doc.char('l')
            + Doc.str(i.toStr())
            + Doc.str(" == ")
            + Doc.char('r')
            + Doc.str(i.toStr())
        i += 1

    rhs


genProduct(typeName: Str, fields: ConFields, tokens: Vec[Token]) Doc:
    match fields:
        ConFields.Empty: Doc.empty()

        ConFields.Named(fields):
            let doc = Doc.empty()
            let i = u32(0)
            for field: (name: Id, ty: Type) in fields.iter():
                if i != 0:
                    doc += Doc.break_(1) + Doc.str("&& ")
                doc += Doc.str("self.")
                    + Doc.str(tokens.get(field.name.token.idx).text)
                    + Doc.str(" == other.")
                    + Doc.str(tokens.get(field.name.token.idx).text)
                i += 1
            doc.nest(4)

        ConFields.Unnamed(_): panic("TODO")


makeLRRecord(l: Doc, r: Doc) Doc:
    Doc.str("(l = ") + l + Doc.str(", r = ") + r + Doc.char(')')


# --------------------------------------------------------------------------------------------------

_interleave(things: Vec[a], toDoc: Fn(a) Doc / exn, sep: Doc) Doc / exn:
    let ret = Doc.empty()
    let i = u32(0)
    for thing: a in things.iter():
        if i != 0:
            ret += sep
        ret += toDoc(thing)
        i += 1
    ret


_brackets(doc: Doc) Doc:
    Doc.char('[') + doc + Doc.char(']')


# --------------------------------------------------------------------------------------------------

test():
    gen("\
type Option[t]:
    None
    Some(t)")

    print("")

    gen("\
type Result[e, t]:
    Err(e)
    Ok(t)")

    print("")

    gen("type Char(_codePoint: U32)")

    print("")

    gen(
        "\
type Token(
    kind: TokenKind,
    text: Str,
    byteIdx: U32,
    line: U32,
    col: U32)",
    )

    print("")

    gen("\
type Foo:
    A(x: U32)
    B(y: Str, z: Bool)")


# args: -iPeg=tools/peg -iCompiler=compiler
# args after: -- --test
# expected stdout:
# impl[Eq[t]] Eq[Option[t]]:
#     __eq(self: Option[t], other: Option[t]) Bool:
#         match (l = self, r = other):
#             (l = Option.None, r = Option.None):
#                 Bool.True
#             (l = Option.Some(l0), r = Option.Some(r0)):
#                 l0 == r0
# 
# impl[Eq[e], Eq[t]] Eq[Result[e, t]]:
#     __eq(self: Result[e, t], other: Result[e, t]) Bool:
#         match (l = self, r = other):
#             (l = Result.Err(l0), r = Result.Err(r0)):
#                 l0 == r0
#             (l = Result.Ok(l0), r = Result.Ok(r0)):
#                 l0 == r0
# 
# impl Eq[Char]:
#     __eq(self: Char, other: Char) Bool:
#         self._codePoint == other._codePoint
# 
# impl Eq[Token]:
#     __eq(self: Token, other: Token) Bool:
#         self.kind == other.kind
#             && self.text == other.text
#             && self.byteIdx == other.byteIdx
#             && self.line == other.line
#             && self.col == other.col
# 
# impl Eq[Foo]:
#     __eq(self: Foo, other: Foo) Bool:
#         match (l = self, r = other):
#             (l = Foo.A(x = l0), r = Foo.A(x = r0)):
#                 l0 == r0
#             (l = Foo.B(y = l0, z = l1), r = Foo.B(y = r0, z = r1)):
#                 l0 == r0 && l1 == r1

