import Lexer
import PegTestLib
import Scanner
import TypeGrammar

main(args: Array[Str]):
    if args.len() < 2:
        panic("") # TODO: print usage

    let mode = args.get(1)
    match mode:
        "--test": test()
        "--item": generate(args.get(2))
        "--file": generate(readFileUtf8(args.get(2)))
        other: print("Unknown mode: `other`")

generate(item: Str):
    let (tokens, error) = tokenize("<ToStr item>", item)
    if error is Option.Some(error):
        panic(lexerErrorStr(error))
    tokens = scan(tokens)
    let result = match try(||: typeDecl(tokens, 0)):
        Result.Err(err): panic("Unable to parse item as type decl: `err`")
        Result.Ok(result): result
    if result.newCursor != tokens.len():
        panic("Parser didn't consume all input, input len = `tokens.len()`, cursor after parsing = `result.newCursor`")
    print(generateTree(result.tree).render(80))

generateTree(parseTree: ParseTree[Token, NonTerminal]) Doc:
    print(parseTree.toDoc().render(80))

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
        panic("TODO")
    else:
        genConAlts(typeName, rhs)

    print(methodBody.render(80))

    let typeName = Doc.str(typeName)
    Doc.nested(
        4,
        Doc.str("impl Eq[") + typeName + Doc.str("]:") + Doc.hardLine()
            + Doc.nested(
                4,
                Doc.str("__eq(self: ") + typeName + Doc.str(", other: ") + typeName + Doc.str(") Bool:") + Doc.hardLine()
                    + methodBody))

genConAlts(typeName: Str, decls: Vec[ParseTree[Token, NonTerminal]]) Doc:
    let doc = Doc.empty()
    for conDecl: ParseTree[Token, NonTerminal] in decls.iter():
        let ts = conDecl.asNonTerminal(NonTerminal.ConDecl)
        let l = genConPat('l', typeName, ts)
        let r = genConPat('r', typeName, ts)
        let pat = makeLRRecord(l, r)
        doc += Doc.nested(
                4,
                pat + Doc.char(':') + Doc.hardLine()
                    + genRhs(typeName, ts))
            + Doc.hardLine()
    doc

genConPat(varPrefix: Char, typeName: Str, nodes: Vec[ParseTree[Token, NonTerminal]]) Doc:
    let conName = Doc.str(nodes.get(0).asTerminal().text)

    if nodes.len() == 1:
        # No fields
        return Doc.str(typeName) + Doc.char('.') + conName

    let fieldPats = if nodes.get(1) is ParseTree.NonTerminal(kind = NonTerminal.NamedFields, nodes):
        generateNamedFieldPats(nodes)
    else:
        generateUnnamedFieldPats(varPrefix, nodes.get(1).asNonTerminal(NonTerminal.UnnamedFields))

    Doc.str(typeName) + Doc.char('.') + conName + Doc.char('(') + fieldPats + Doc.char(')')

generateNamedFieldPats(fieldNodes: Vec[ParseTree[Token, NonTerminal]]) Doc:
    let fieldName = fieldNodes.get(0).asTerminal().text
    let fieldType = fieldNodes.get(1)
    Doc.empty()

generateUnnamedFieldPats(varPrefix: Char, fieldNodes: Vec[ParseTree[Token, NonTerminal]]) Doc:
    let doc = Doc.empty()
    let i = 0u32
    for fieldNode: ParseTree[Token, NonTerminal] in fieldNodes.iter():
        if i != 0:
            doc += Doc.str(", ")
        doc += Doc.char(varPrefix) + Doc.str(i.toStr())
    doc

generateUnnamedFieldsBody(conName: Doc, numFields: U32) Doc:
    let doc = conName + Doc.char('(')
    for i: U32 in range(0u32, numFields):
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
    for i: U32 in range(0u32, numFields):
        if i != 0:
            rhs += Doc.str(" && ")
        rhs += Doc.char('l') + Doc.str(i.toStr()) + Doc.str(" == ")
            + Doc.char('r') + Doc.str(i.toStr())
    rhs

makeLRRecord(l: Doc, r: Doc) Doc:
    Doc.str("(l = ") + l + Doc.str(", r = ") + r + Doc.char(')')

type MatchBuilder:
    scrut: Doc
    alts: Vec[(pat: Doc, body: Doc)]

MatchBuilder.withScrut(scrut: Doc) MatchBuilder:
    MatchBuilder(scrut, alts = Vec.withCapacity(5))

MatchBuilder.alt(self, pat: Doc, body: Doc) MatchBuilder:
    self.alts.push((pat = pat, body = body))
    self

MatchBuilder.render(self) Doc:
    let alts = Doc.empty()
    for alt: (pat: Doc, body: Doc) in self.alts.iter():
        alts += Doc.nested(4, alt.pat + Doc.char(':') + Doc.break_(1) + alt.body).group()
    Doc.nested(4, Doc.str("match ") + self.scrut + Doc.char(':') + Doc.hardLine() + alts)

test():
    print("Running ToStr derive tests...")

# --------------------------------------------------------------------------------------------------

_interleave(things: Vec[a], toDoc: Fn(a) Doc / exn, sep: Doc) Doc / exn:
    let ret = Doc.empty()
    let i = 0u32
    for thing: a in things.iter():
        if i != 0:
            ret += sep
        ret += toDoc(thing)
        i += 1
    ret
