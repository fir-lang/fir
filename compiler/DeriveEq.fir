import Lexer
import PegTestLib
import Scanner
import TypeGrammar

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
        panic(lexerErrorStr(error))

    tokens = match try(||: scan[row[]](tokens)):
        Result.Err(~ScannerError(line, col, msg)):
            panic("Scanner error: `line + 1`:`col + 1`: `msg`")
        Result.Ok(tokens):
            tokens

    let result = match try(||: typeDecl(tokens, 0)):
        Result.Err(err): panic("Unable to parse item as type decl: `err`")
        Result.Ok(result): result

    if result.newCursor != tokens.len():
        panic("Parser didn't consume all input, input len = `tokens.len()`, cursor after parsing = `result.newCursor`")

    print(genTree(result.tree).render(80))

genTree(parseTree: ParseTree[Token, NonTerminal]) Doc:
    # print(parseTree.toDoc().render(80))

    let nodes = parseTree.asNonTerminal(NonTerminal.TypeDecl)

    let typeName = nodes.get(0).asTerminal().text

    let rhsIdx: U32 = 0
    let typeParams: Vec[Str] = if nodes.get(1) is ParseTree.NonTerminal(kind = NonTerminal.TypeParams, nodes):
        rhsIdx = 2
        let argStrs: Vec[Str] = Vec.withCapacity(nodes.len())
        for node: ParseTree[Token, NonTerminal] in nodes.iter():
            argStrs.push(node.asTerminal().text)
        argStrs
    else:
        rhsIdx = 1
        Vec.withCapacity(0)

    # NamedFields in products, or ConDecls in sums.
    let rhs = nodes.get(rhsIdx).asNonTerminal(NonTerminal.TypeDeclRhs)
    let methodBody = if rhs.get(0) is ParseTree.NonTerminal(kind = NonTerminal.NamedField, ..):
        genProduct(typeName, rhs)
    else:
        genSumAlts(typeName, rhs)

    let typeName = Doc.str(typeName)

    let preds = Doc.empty()
    if typeParams.len() != 0:
        preds = _brackets(_interleave(
            typeParams,
            |param|: Doc.str("Eq[") + Doc.str(param) + Doc.char(']'),
            Doc.str(", ")
        ))

    let typeParamsDoc = Doc.empty()
    if typeParams.len() != 0:
        typeParamsDoc = _brackets(_interleave(typeParams, Doc.str, Doc.str(", ")))

    Doc.nested(
        4,
        Doc.str("impl") + preds + Doc.str(" Eq[") + typeName + typeParamsDoc + Doc.str("]:") + Doc.hardLine()
            + Doc.nested(
                4,
                Doc.str("__eq(self: ") + typeName + Doc.str(", other: ") + typeName + Doc.str(") Bool:") + Doc.hardLine()
                    + methodBody))

genSumAlts(typeName: Str, decls: Vec[ParseTree[Token, NonTerminal]]) Doc:
    let doc = Doc.empty()
    let i = u32(0)
    for conDecl: ParseTree[Token, NonTerminal] in decls.iter():
        if i != 0:
            doc += Doc.hardLine()
        i += 1
        let ts = conDecl.asNonTerminal(NonTerminal.ConDecl)
        let l = genConPat('l', typeName, ts)
        let r = genConPat('r', typeName, ts)
        let pat = makeLRRecord(l, r)
        doc += Doc.nested(
                4,
                pat + Doc.char(':') + Doc.hardLine()
                    + genRhs(typeName, ts))
    doc

genConPat(varPrefix: Char, typeName: Str, nodes: Vec[ParseTree[Token, NonTerminal]]) Doc:
    let conName = Doc.str(nodes.get(0).asTerminal().text)

    if nodes.len() == 1:
        # No fields
        return Doc.str(typeName) + Doc.char('.') + conName

    let fieldPats = if nodes.get(1) is ParseTree.NonTerminal(kind = NonTerminal.NamedFields, nodes):
        genNamedFieldPats(nodes)
    else:
        genUnnamedFieldPats(varPrefix, nodes.get(1).asNonTerminal(NonTerminal.UnnamedFields))

    Doc.str(typeName) + Doc.char('.') + conName + Doc.char('(') + fieldPats + Doc.char(')')

genNamedFieldPats(fieldNodes: Vec[ParseTree[Token, NonTerminal]]) Doc:
    let fieldName = fieldNodes.get(0).asTerminal().text
    let fieldType = fieldNodes.get(1)
    Doc.empty()

genUnnamedFieldPats(varPrefix: Char, fieldNodes: Vec[ParseTree[Token, NonTerminal]]) Doc:
    let doc = Doc.empty()
    for i: U32 in range(u32(0), fieldNodes.len()):
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

genRhs(typeName: Str, nodes: Vec[ParseTree[Token, NonTerminal]]) Doc:
    let conName = Doc.str(nodes.get(0).asTerminal().text)

    if nodes.len() == 1:
        # No fields
        return Doc.str("Bool.True")

    let numFields = if nodes.get(1) is ParseTree.NonTerminal(kind = NonTerminal.NamedFields, nodes):
        nodes.len()
    else:
        nodes.get(1).asNonTerminal(NonTerminal.UnnamedFields).len()

    let rhs = Doc.empty()
    for i: U32 in range(u32(0), numFields):
        if i != 0:
            rhs += Doc.str(" && ")
        rhs += Doc.char('l') + Doc.str(i.toStr()) + Doc.str(" == ")
            + Doc.char('r') + Doc.str(i.toStr())
        i += 1
    rhs

genProduct(typeName: Str, decls: Vec[ParseTree[Token, NonTerminal]]) Doc:
    let doc = Doc.empty()
    let i = u32(0)
    for field: ParseTree[Token, NonTerminal] in decls.iter():
        if i != 0:
            doc += Doc.break_(1) + Doc.str("&& ")
        let fieldName = Doc.str(field.asNonTerminal(NonTerminal.NamedField).get(0).asTerminal().text)
        doc += Doc.str("self.") + fieldName + Doc.str(" == other.") + fieldName
        i += 1
    doc.nest(4)

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
type Result[e, r]:
    Ok(r)
    Err(e)")

    print("")

    gen("\
type Char:
    _codePoint: U32")

    print("")

    gen("\
type Token:
    kind: TokenKind
    text: Str
    byteIdx: U32
    line: U32
    col: U32")

# args after: -- --test
# expected stdout:
# impl[Eq[t]] Eq[Option[t]]:
#     __eq(self: Option, other: Option) Bool:
#         (l = Option.None, r = Option.None):
#             Bool.True
#         (l = Option.Some(l0), r = Option.Some(r0)):
#             l0 == r0
# 
# impl[Eq[e], Eq[r]] Eq[Result[e, r]]:
#     __eq(self: Result, other: Result) Bool:
#         (l = Result.Ok(l0), r = Result.Ok(r0)):
#             l0 == r0
#         (l = Result.Err(l0), r = Result.Err(r0)):
#             l0 == r0
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
