import Compiler.Lexer
import Compiler.ParseTree
import Compiler.Scanner
import Compiler.Token
import PegGrammar

main(args: Array[Str]):
    if args.len() != 2:
        panic("Usage: Peg.fir <peg file>")

    let input = args.get(1)
    let contents = readFileUtf8(input)
    let (tokens, error) = tokenize(input, contents)

    if error is Option.Some(error):
        panic(errStr(error))

    let tokens = match try(||: scan[row[]](tokens)):
        Result.Err(~ScannerError(line, col, msg)):
            panic("Unable to scan file: `line + 1`:`col + 1`: `msg`")
        Result.Ok(tokens):
            tokens

    if tokens.len() == 0:
        panic("Empty file")

    let grammar = match try(||: grammar(tokens, 0)):
        Result.Err(ParseError.UnexpectedEof):
            panic("Unexpected end of input")
        Result.Err(ParseError.UnexpectedToken(cursor)):
            panic("Unexpected token `tokens.get(cursor)`")
        Result.Ok(result):
            if result.newCursor != tokens.len():
                print(result.tree.toDoc().render(80))
                let lastToken = tokens.get(result.newCursor)
                panic("Left over tokens (cursor = `result.newCursor`, tokens = `tokens.len()`, last token = `lastToken`)")
            # print(result.tree.toDoc().render(80))
            convertParseTree(result.tree)

    let terminalPats: HashMap[Str, Vec[Token]] = HashMap.withCapacity(grammar.terminalsDecl.terminals.len() * 2)
    for terminalDecl: TerminalDecl in grammar.terminalsDecl.terminals.iter():
        terminalPats.insert(terminalDecl.name.substr(1, terminalDecl.name.len() - 1), terminalDecl.pattern)

    let nonTerminalNames: Vec[Str] = Vec.withCapacity(grammar.nonTerminalDecls.len())
    for nonTerminal: NonTerminalDecl in grammar.nonTerminalDecls.iter():
        nonTerminalNames.push(nonTerminal.name)

    print("# This is generated file, do not edit.")
    print("")

    for import_: Str in grammar.imports.iter():
        print("import `import_`")

    if grammar.imports.len() != 0:
        print("")

    print(generateNonTerminalType(grammar.nonTerminalType, nonTerminalNames).render(80))
    print("")
    print(generateNonTerminalToStr(grammar.nonTerminalType, nonTerminalNames).render(80))
    print("")
    print(generateNonTerminalEq(grammar.nonTerminalType, nonTerminalNames).render(80))
    print("")

    let nonTerminalDeclIdx = 0
    for nonTerminalDecl: NonTerminalDecl in grammar.nonTerminalDecls.iter():
        if nonTerminalDeclIdx != 0:
            print("")
        let doc = generateNonTerminal(grammar.terminalType, grammar.nonTerminalType, nonTerminalDecl, terminalPats)
        print(doc.render(80))
        nonTerminalDeclIdx += 1

errStr(err: Error) Str:
    "`err.loc.file`:`err.loc.line + 1`:`err.loc.col + 1`: `err.msg`"

capitalize(s: Str) Str / exn:
    let buf = StrBuf.withCapacity(s.len())
    let chars = s.chars()

    if chars.next[CharIter, Char, exn]() is Option.Some(char):
        buf.push(char.toAsciiUppercase())

    while chars.next() is Option.Some(char):
        buf.push(char)

    buf.toStr()

# --------------------------------------------------------------------------------------------------
# Parsing PEG specs

type Grammar:
    imports: Vec[Str]
    terminalType: Str
    nonTerminalType: Str
    terminalsDecl: TerminalsDecl
    nonTerminalDecls: Vec[NonTerminalDecl]

convertParseTree(tree: ParseTree[Token, NonTerminal]) Grammar:
    let grammar = tree.asNonTerminal(NonTerminal.Grammar)

    # This code is a bit hacky.. We used to have a proper AST type that we kept after bootstrapping,
    # but that AST didn't have imports and types, and I don't want make it more complicated. So for
    # now we print the imports directly and generate the AST for the rest.
    let importDecls = grammar.get(0).asNonTerminal(NonTerminal.ImportDecls)
    let imports: Vec[Str] = Vec.withCapacity(importDecls.len())
    let importStr = StrBuf.withCapacity(50)
    for importDecl: ParseTree[Token, NonTerminal] in importDecls.iter():
        let importDeclNodes = importDecl.asNonTerminal(NonTerminal.ImportDecl)
        importStr.clear()
        for i: U32 in range(u32(0), importDeclNodes.len()):
            if i != 0:
                importStr.push('.')
            importStr.pushStr(importDeclNodes.get(i).asTerminal().text)
        imports.push(importStr.toStr())

    let typeDecls = grammar.get(1).asNonTerminal(NonTerminal.TypeDecls)
    let terminalType: Option[Str] = Option.None
    let nonTerminalType: Option[Str] = Option.None
    for typeDecl: ParseTree[Token, NonTerminal] in typeDecls.iter():
        let nodes = typeDecl.asNonTerminal(NonTerminal.TypeDecl)
        let typeName = nodes.get(0).asTerminal().text
        let typeValue = nodes.get(1).asTerminal().text
        match typeName:
            "Terminal":
                if terminalType is Option.Some(_):
                    panic("Terminal type declared multiple times.")
                terminalType = Option.Some(typeValue)
            "NonTerminal":
                if nonTerminalType is Option.Some(_):
                    panic("Non-terminal type declared multiple times.")
                nonTerminalType = Option.Some(typeValue)
            other:
                panic("Unknown type declaration: `other`")

    if terminalType is Option.None:
        panic("Terminal type is not defined")

    if nonTerminalType is Option.None:
        panic("Non-terminal type is not defined")

    let terminalsDecl = grammar.get(2).asNonTerminal(NonTerminal.TerminalsDecl)
    let terminalsDecl = convertTerminalsDecl(terminalsDecl)

    let nonTerminalDecls = grammar.get(3).asNonTerminal(NonTerminal.NonTerminalDecls)
    let converted: Vec[NonTerminalDecl] = Vec.withCapacity(nonTerminalDecls.len())
    for decl: ParseTree[Token, NonTerminal] in nonTerminalDecls.iter():
        converted.push(convertNonTerminalDecl(decl.asNonTerminal(NonTerminal.NonTerminalDecl)))

    Grammar(
        imports,
        terminalType = terminalType.unwrap(),
        nonTerminalType = nonTerminalType.unwrap(),
        terminalsDecl,
        nonTerminalDecls = converted,
    )

convertTerminalsDecl(nodes: Vec[ParseTree[Token, NonTerminal]]) TerminalsDecl:
    let terminals: Vec[TerminalDecl] = Vec.withCapacity(nodes.len())

    for node: ParseTree[Token, NonTerminal] in nodes.iter():
        let node = node.asNonTerminal(NonTerminal.TerminalDecl)
        let name = node.get(0).asTerminal().text
        let pattern: Vec[Token] = Vec.withCapacity(node.len() - 1)
        for tok: ParseTree[Token, NonTerminal] in node.iter().skip(1):
            pattern.push(tok.asTerminal())
        terminals.push(TerminalDecl(name, pattern))

    TerminalsDecl(terminals)

convertNonTerminalDecl(nodes: Vec[ParseTree[Token, NonTerminal]]) NonTerminalDecl:
    let name = nodes.get(0).asTerminal().text

    let alts: Vec[Alt] = Vec.withCapacity(nodes.len() - 1)

    for altTree: ParseTree[Token, NonTerminal] in nodes.iter().skip(1):
        let altTreeNodes = altTree.asNonTerminal(NonTerminal.NonTerminalAlt)
        alts.push(convertAlt(altTreeNodes))

    NonTerminalDecl(name, alts)

convertAlt(nodes: Vec[ParseTree[Token, NonTerminal]]) Alt:
    let symbols: Vec[Symbol] = Vec.withCapacity(nodes.len())

    for symbolTree: ParseTree[Token, NonTerminal] in nodes.iter():
        symbols.push(convertSymbol(symbolTree.asNonTerminal(NonTerminal.Symbol)))

    Alt(symbols)

convertSymbol(nodes: Vec[ParseTree[Token, NonTerminal]]) Symbol:
    let symbolIdx: U32 = if nodes.get(0) is ParseTree.NonTerminal(kind = NonTerminal.SymbolPrefix, ..):
        1
    else:
        0

    let symbolTree = nodes.get(symbolIdx)

    if symbolTree is ParseTree.Terminal(Token(kind = TokenKind.Dollar,..)):
        return Symbol.EndOfInput


    let symbol = convertSymbolNonRec(symbolTree.asNonTerminal(NonTerminal.SymbolNonRec))

    if nodes.len() > symbolIdx + 1:
        match nodes.get(symbolIdx + 1).asNonTerminal(NonTerminal.SymbolSuffix).get(0).asTerminal().kind:
            TokenKind.Star: symbol = Symbol.ZeroOrMore(symbol)
            TokenKind.Plus: symbol = Symbol.OneOrMore(symbol)
            TokenKind.Question: symbol = Symbol.Optional(symbol)
            _: panic("")

    if nodes.get(0) is ParseTree.NonTerminal(kind = NonTerminal.SymbolPrefix, nodes):
        match nodes.get(0).asTerminal().kind:
            TokenKind.Minus: symbol = Symbol.NegLookahead(symbol)
            TokenKind.Underscore: symbol = Symbol.Ignore(symbol)
            _: panic("")

    symbol

convertSymbolNonRec(nodes: Vec[ParseTree[Token, NonTerminal]]) Symbol:
    if nodes.len() == 1:
        let terminal = nodes.get(0).asTerminal()
        match terminal.kind:
            TokenKind.LowerId: Symbol.NonTerminal(terminal.text)
            TokenKind.Str: Symbol.Terminal(terminal.text.substr(1, terminal.text.len() - 1))
            _: panic("")
    else:
        let symbols: Vec[Symbol] = Vec.withCapacity(nodes.len())
        for node: ParseTree[Token, NonTerminal] in nodes.iter():
            symbols.push(convertSymbol(node.asNonTerminal(NonTerminal.Symbol)))
        Symbol.Group(symbols)

## A declaration in a PEG spec.
type TopDecl:
    ## Declares terminals in the grammar.
    ##
    ## A grammar needs to have one `Terminals` declaration.
    Terminals(TerminalsDecl)

    ## Declares a non-terminal in the grammar.
    NonTerminal(NonTerminalDecl)

## Declares terminals in the grammar.
type TerminalsDecl:
    terminals: Vec[TerminalDecl]

## A terminal declaration. E.g. in
##
## ```
## "Foo" = Token(kind = TokenKind.Foo, ..)
## ```
##
## `name` will be `"Foo"`, `pattern` will be the tokens for the right-hand side of the equation.
##
## At least for now, we don't parse the pattern and make sure it's a valid Fir pattern. If the
## pattern has syntax or type errors, we will still generate the code, and the generated code will
## have syntax or type errors too.
type TerminalDecl:
    name: Str
    pattern: Vec[Token]

## A non-terminal declaration. E.g. in
##
## ```
## jsonObject:
##     "{" "}"
##     "{" pair ("," pair)* "}"
## ```
##
## `name` is `"jsonObject"`, and `alts` is the two alternatives.
type NonTerminalDecl:
    name: Str
    alts: Vec[Alt]

## Alternatives of a non-terminal.
type Alt:
    symbols: Vec[Symbol]

## A symbol in an alternative.
type Symbol:
    ## A terminal. E.g. `Foo` above.
    Terminal(Str)

    ## A non-terminal. E.g. `jsonObject` above.
    NonTerminal(Str)

    ## Groups a list of symbols together. Parsed from parenthesized expressions: `("," pair)`.
    Group(Vec[Symbol])

    ## Parses the symbol zero or more times. Parsed from `*` suffix.
    ZeroOrMore(Symbol)

    ## Parses the symbol one or more times. Parsed from `+` suffix.
    OneOrMore(Symbol)

    ## Parses the symbol one or one times. Parsed from `?` suffix.
    Optional(Symbol)

    ## Parses the symbol, but does not add the parsed terminals and non-terminals to the tree.
    ## Parsed from `_` prefix.
    Ignore(Symbol)

    ## Negative lookahead: succeeds without incrementing the cursor if parsing fails. Parsed from
    ## `-` prefix.
    NegLookahead(Symbol)

    ## Succeeds when the cursor is at the end. Fails with "unexpected token" otherwise.
    EndOfInput

# --------------------------------------------------------------------------------------------------
# Code generation

generateNonTerminalType(typeName: Str, nonTerminalNames: Vec[Str]) Doc:
    let doc = Doc.str("type `typeName`:")
    for name: Str in nonTerminalNames.iter():
        doc += Doc.hardLine() + Doc.str(capitalize(name))
    doc.nest(4)

generateNonTerminalToStr(typeName: Str, nonTerminalNames: Vec[Str]) Doc:
    let doc = Doc.str("impl ToStr[`typeName`]:")
    doc += Doc.hardLine()

    let fnDoc = Doc.str("toStr(self: `typeName`) Str:")
    fnDoc += Doc.hardLine()

    let matchDoc = Doc.str("match self:")
    for name: Str in nonTerminalNames.iter():
        let capitalName = capitalize(name)
        matchDoc += Doc.hardLine() + Doc.str("`typeName`.`capitalName`: \"`capitalName`\"")

    (doc + (fnDoc + matchDoc.nest(4)).nest(4)).nest(4)

generateNonTerminalEq(typeName: Str, nonTerminalNames: Vec[Str]) Doc:
    let doc = Doc.str("impl Eq[`typeName`]:")
    doc += Doc.hardLine()

    let fnDoc = Doc.str("__eq(self: `typeName`, other: `typeName`) Bool:")
    fnDoc += Doc.hardLine()

    let matchDoc = Doc.str("match (left = self, right = other):")
    for name: Str in nonTerminalNames.iter():
        let capitalName = capitalize(name)
        matchDoc += Doc.hardLine() + Doc.str("(left = `typeName`.`capitalName`, right = `typeName`.`capitalName`): Bool.True")
    matchDoc += Doc.hardLine() + Doc.str("_: Bool.False")

    (doc + (fnDoc + matchDoc.nest(4)).nest(4)).nest(4)

generateNonTerminal(terminalType: Str, nonTerminalType: Str, decl: NonTerminalDecl, terminalPats: HashMap[Str, Vec[Token]]) Doc / exn:
    let doc = Doc.str("`decl.name`(tokens: Vec[`terminalType`], cursor: U32) \
                            (tree: ParseTree[`terminalType`, `nonTerminalType`], newCursor: U32) / ParseError[`terminalType`]:")
                + Doc.hardLine()

    doc += Doc.str("let cursor0 = cursor") + Doc.hardLine()
    doc += Doc.str("let curErr: Option[ParseError[`terminalType`]] = Option.None") + Doc.hardLine()

    # TODO: Count the non-ignored symbols, allocate vector (or maybe array) with the right size.
    doc += Doc.str("let nodes: Vec[ParseTree[`terminalType`, `nonTerminalType`]] = Vec.empty()") + Doc.hardLine()

    for alt: Alt in decl.alts.iter():
        let altResultDoc = Doc.str("let altResult = try(||:") + Doc.hardLine()
        for symbol: Symbol in alt.symbols.iter():
            altResultDoc += generateSymbolParser(symbol, Bool.False, terminalPats) + Doc.hardLine()
        altResultDoc += Doc.str("cursor")
        altResultDoc = altResultDoc.nest(4)
        altResultDoc += Doc.hardLine() + Doc.str(")") + Doc.hardLine()
        doc += altResultDoc

        let altResultMatchDoc = Doc.str("match altResult:") + Doc.hardLine()

        let errAlt =
            Doc.nested(
                4,
                Doc.str("Result.Err(err):")
                    + Doc.hardLine()
                    + makeUpdateError()
                    + Doc.hardLine()
                    + Doc.str("cursor = cursor0")
                    + Doc.hardLine()
                    + Doc.str("nodes.clear()"))

        let okAlt =
            Doc.nested(
                4,
                Doc.str("Result.Ok(newCursor):")
                    + Doc.hardLine()
                    + Doc.str("return (tree = ParseTree.NonTerminal(kind = `nonTerminalType`.`capitalize(decl.name)`, nodes), newCursor = newCursor)"))

        altResultMatchDoc = Doc.nested(4, altResultMatchDoc + errAlt) + Doc.nested(4, Doc.hardLine() + okAlt)

        doc += altResultMatchDoc + Doc.hardLine()

    doc +=
        Doc.nested(
            4,
            Doc.str("if cursor == tokens.len():")
                + Doc.hardLine()
                + makeThrowUnexpectedEof())
        + Doc.hardLine()
        + Doc.nested(
            4,
            Doc.str("else:")
                + Doc.hardLine()
                + makeThrow(
                    Doc.nested(
                        4,
                        Doc.str("curErr.unwrapOrElse(||:")
                            + Doc.hardLine()
                            + makeUnexpectedTokenError(Doc.str("cursor"))
                            + Doc.char(')'))))

    doc.nest(4)

## Generate code for matching a single symbol.
##
## Throws a `ParseError` if matching fails.
##
## Matched values will be pushed to a variable called `nodes`, which should be a
## `Vec[ParseTree[...]]` with the right terminal and non-terminal type arguments.
##
## Generated `Doc`s don't end with a hard-line, so these can be nested in other `Doc`s without
## adding an empty indented line at the end.
##
## Note: this updates the variable `cursor`, but since symbol matching is always done in a closure
## in a `try` block, the `cursor` won't update the non-terminal function's `cursor` variable. The
## use site of this function should return the value of `cursor` from the closure so that the
## non-terminal function's `cursor` can be updated with the new value.
generateSymbolParser(symbol: Symbol, ignore: Bool, terminalPats: HashMap[Str, Vec[Token]]) Doc / exn:
    match symbol:
        Symbol.Terminal(terminal):
            let patToks = terminalPats.get(terminal).unwrapOrElse(||: panic("Unknown terminal: `terminal`"))

            let eofCheck =
                Doc.nested(
                    4,
                    Doc.str("if cursor == tokens.len():")
                        + Doc.hardLine()
                        + makeThrowUnexpectedEof())

            eofCheck += Doc.hardLine()

            let tokenKindCheck = Doc.str("if tokens.get(cursor) is ")
                + tokensToCode(patToks)
                + Doc.char(':')
                + Doc.hardLine()

            let nested = Doc.empty()
            if not ignore:
                nested += Doc.str("nodes.push(ParseTree.Terminal(tokens.get(cursor)))") + Doc.hardLine()
            nested += Doc.str("cursor += 1")

            tokenKindCheck = Doc.nested(4, tokenKindCheck + nested) + Doc.hardLine()

            tokenKindCheck +=
                Doc.nested(
                    4,
                    Doc.str("else:")
                        + Doc.hardLine()
                        + makeThrow(makeUnexpectedTokenError(Doc.str("cursor"))))

            eofCheck + tokenKindCheck

        Symbol.NonTerminal(nonTerminal):
            let doc = Doc.str("let nonTerminalResult = `nonTerminal`(tokens, cursor)")
                + Doc.hardLine()
                + Doc.str("cursor = nonTerminalResult.newCursor")

            if not ignore:
                doc += Doc.hardLine() + Doc.str("nodes.push(nonTerminalResult.tree)")

            doc

        Symbol.Group(symbols):
            let doc = Doc.empty()
            let symIdx: U32 = 0
            for symbol: Symbol in symbols.iter():
                if symIdx != 0:
                    doc += Doc.hardLine()
                doc += generateSymbolParser(symbol, ignore, terminalPats)
                symIdx += 1
            doc

        Symbol.ZeroOrMore(symbol):
            Doc.nested(
                4,
                Doc.str("loop:")
                    + Doc.hardLine()
                    + Doc.str("let nodesLen0 = nodes.len()")
                    + Doc.hardLine()
                    + Doc.nested(
                        4,
                        Doc.str("let symResult = try(||:")
                            + Doc.hardLine()
                            + generateSymbolParser(symbol, ignore, terminalPats)
                            + Doc.hardLine()
                            + Doc.str("cursor"))
                    + Doc.hardLine()
                    + Doc.str(")")
                    + Doc.hardLine()
                    + Doc.nested(
                          4,
                          Doc.str("match symResult:")
                              + Doc.hardLine()
                              + Doc.nested(
                                  4,
                                  Doc.str("Result.Err(err):")
                                      + Doc.hardLine()
                                      + makeUpdateError()
                                      + Doc.hardLine()
                                      + Doc.str("nodes.truncate(nodesLen0)")
                                      + Doc.hardLine()
                                      + Doc.str("break"))
                              + Doc.hardLine()
                              + Doc.nested(
                                  4,
                                  Doc.str("Result.Ok(newCursor):")
                                      + Doc.hardLine()
                                      + Doc.str("cursor = newCursor"))))

        Symbol.OneOrMore(symbol):
            generateSymbolParser(symbol, ignore, terminalPats)
                + Doc.hardLine()
                + generateSymbolParser(Symbol.ZeroOrMore(symbol), ignore, terminalPats)

        Symbol.Optional(symbol):
            Doc.str("let nodesLen0 = nodes.len()")
                + Doc.hardLine()
                + Doc.nested(
                      4,
                      Doc.str("let symResult = try(||:")
                          + Doc.hardLine()
                          + generateSymbolParser(symbol, ignore, terminalPats)
                          + Doc.hardLine()
                          + Doc.str("cursor"))
                 + Doc.hardLine()
                 + Doc.str(")")
                 + Doc.hardLine()
                 + Doc.nested(
                       4,
                       Doc.str("match symResult:")
                           + Doc.hardLine()
                           + Doc.nested(
                               4,
                               Doc.str("Result.Err(err):")
                                   + Doc.hardLine()
                                   + makeUpdateError()
                                   + Doc.hardLine()
                                   + Doc.str("nodes.truncate(nodesLen0)"))
                           + Doc.hardLine()
                           + Doc.nested(
                                   4,
                                   Doc.str("Result.Ok(newCursor):")
                                       + Doc.hardLine()
                                       + Doc.str("cursor = newCursor")))

        Symbol.Ignore(symbol):
            generateSymbolParser(symbol, Bool.True, terminalPats)

        Symbol.NegLookahead(symbol):
            let doc = Doc.str("let tokensLen0 = tokens.len()") + Doc.hardLine()
            doc + Doc.nested(
                4,
                Doc.str("let symResult = try(||:")
                    + Doc.hardLine()
                    + generateSymbolParser(symbol, Bool.True, terminalPats))
                + Doc.hardLine()
                + Doc.str(")")
                + Doc.hardLine()
                + Doc.nested(
                    4,
                    Doc.str("match symResult:")
                        + Doc.hardLine()
                        + Doc.nested(
                            4,
                            Doc.str("Result.Err(err):")
                                + Doc.hardLine()
                                + makeUpdateError()
                                + Doc.hardLine()
                                + Doc.str("tokens.truncate(tokensLen0)"))
                        + Doc.hardLine()
                        + Doc.nested(
                            4,
                            Doc.str("Result.Ok(_):")
                                + Doc.hardLine()
                                + makeThrow(makeUnexpectedTokenError(Doc.str("cursor")))))

        Symbol.EndOfInput:
            Doc.nested(
                4,
                Doc.str("if cursor == tokens.len():")
                    + Doc.hardLine()
                    + Doc.str("cursor"))
                + Doc.hardLine()
                + Doc.nested(
                    4,
                    Doc.str("else:")
                        + Doc.hardLine()
                        + makeThrow(makeUnexpectedTokenError(Doc.str("cursor"))))


tokensToCode(tokens: Vec[Token]) Doc / exn:
    if tokens.len() == 0:
        panic("tokensToCode: empty tokens")

    let out = StrBuf.withCapacity(tokens.len() * 3)

    let lastLine = tokens.get(0).line
    let lastCol = tokens.get(0).col

    for token: Token in tokens.iter():
        if token.line != lastLine:
            panic("tokensToCode: tokens span multiple lines")

        while lastCol < token.col:
            out.push(' ')
            lastCol += 1

        out.pushStr(token.text)

        # TODO: We could iterate the text once, increment column and push chars.
        lastCol += token.text.chars().count[CharIter, Char, exn]()

    Doc.str(out.toStr())

makeUnexpectedTokenError(cursor: Doc) Doc:
    Doc.group(
        Doc.nested(
            4,
            Doc.group(
                Doc.str("ParseError.UnexpectedToken(")
                    + Doc.break_(0)
                    + Doc.str("cursor = ") + cursor))
            + Doc.whenNotFlat(Doc.char(','))
            + Doc.break_(0)
            + Doc.str(")"))

makeThrow(expr: Doc) Doc:
    Doc.nested(4, Doc.str("throw(") + Doc.break_(0) + expr + Doc.char(')')).group()

makeThrowUnexpectedEof() Doc:
    makeThrow(Doc.str("ParseError.UnexpectedEof"))

# When generating code that backtracks, update the local `curErr: Option[ParseError[t]]` if the new
# error's cursor is more advanced than the current.
#
# The new error value should be named `err`.
makeUpdateError() Doc:
    Doc.nested(
        4,
        Doc.str("match curErr:")
            + Doc.hardLine()
            + Doc.nested(
                4,
                Doc.str("Option.None:")
                    + Doc.hardLine()
                    + Doc.str("curErr = Option.Some(err)"))
            + Doc.hardLine()
            + Doc.nested(
                4,
                Doc.str("Option.Some(curErr_):")
                    + Doc.hardLine()
                    + Doc.str("curErr = Option.Some(ParseError.takeAdvanced(curErr_, err))")))
