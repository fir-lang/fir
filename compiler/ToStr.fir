import Lexer
import PegTestLib
import Scanner
import TypeGrammar

main(args: Array[Str])
    if args.len() < 2:
        panic("") # TODO: print usage

    let mode = args.get(1)
    match mode:
        "--test": test()
        "--item": generate(args.get(2))
        "--file": generate(readFileUtf8(args.get(2)))

generate(item: Str)
    let (tokens, error) = tokenize("<ToStr item>", item)
    if error is Option.Some(error):
        panic(lexerErrorStr(error))
    tokens = scan(tokens)
    let result = match try({ typeDecl(tokens, 0) }):
        Result.Err(err): panic("Unable to parse item as type decl: `err`")
        Result.Ok(result): result
    if result.newCursor != tokens.len():
        panic("Parser didn't consume all input, input len = `tokens.len()`, cursor after parsing = `result.newCursor`")
    generateTree(result.tree)

generateTree(parseTree: ParseTree[Token, NonTerminal])
    print(parseTree.toDoc().print(80))

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
        generateNamedFields(rhs)
    else:
        generateConDecls(typeName, rhs)

    ()

generateConDecls(typeName: Str, decls: Vec[ParseTree[Token, NonTerminal]]): Doc
    let doc = Doc.empty()
    for conDecl: ParseTree[Token, NonTerminal] in decls.iter():
        doc += generateConDecl(typeName, conDecl.asNonTerminal(NonTerminal.ConDecl))
    doc

generateConDecl(typeName: Str, nodes: Vec[ParseTree[Token, NonTerminal]]): Doc
    let conName = nodes.get(0).asTerminal().text

    if nodes.len() == 1:
        return Doc.nested(
            4,
            Doc.str(typeName) + Doc.char('.') + Doc.str(conName) + Doc.char(':')
                + Doc.break_(1)
                + Doc.char('"') + Doc.str(conName) + Doc.char('"'))

    let fieldsDoc = if nodes.get(1) is ParseTree.NonTerminal(kind = NonTerminal.NamedFields, nodes):
        generateNamedFields(nodes)
    else:
        generateUnnamedFields(nodes.get(1).asNonTerminal(NonTerminal.UnnamedFields))

    panic("TODO")

generateNamedFields(fieldNodes: Vec[ParseTree[Token, NonTerminal]]): Doc
    let fieldName = fieldNodes.get(0).asTerminal().text
    let fieldType = fieldNodes.get(1)
    Doc.empty()

generateUnnamedFields(fieldNodes: Vec[ParseTree[Token, NonTerminal]]): Doc
    Doc.empty()

generateType(nodes: Vec[ParseTree[Token, NonTerminal]]): Doc
    Doc.str("TODO")

type MatchBuilder:
    scrut: Doc
    alts: Vec[(pat: Doc, body: Doc)]

MatchBuilder.withScrut(scrut: Doc): MatchBuilder
    MatchBuilder(scrut, alts = Vec.withCapacity(5))

MatchBuilder.alt(self, pat: Doc, body: Doc): MatchBuilder
    self.alts.push((pat = pat, body = body))
    self

MatchBuilder.render(self): Doc
    let alts = Doc.empty()
    for alt: (pat: Doc, body: Doc) in self.alts.iter():
        alts += Doc.nested(4, alt.pat + Doc.char(':') + Doc.break_(1) + alt.body).group()
    Doc.nested(4, Doc.str("match ") + self.scrut + Doc.char(':') + Doc.hardLine() + alts)

test()
    print("Running ToStr derive tests...")
