import Lexer
import ParseTree
import PegGrammar
import Scanner
import Token

main(args: Array[Str])
    if args.len() != 2:
        panic("Usage: Peg.fir <peg file>")

    let input = args.get(1)
    let contents = readFileUtf8(input)
    let (tokens, error) = tokenize(input, contents)
    if error is Option.Some(error):
        panic(errStr(error))
    let tokens = scan(tokens)

    if tokens.len() == 0:
        panic("Empty file")

    let decls = match try({ topDecls(tokens, 0) }):
        Result.Err(err):
            panic(err)
        Result.Ok(result):
            if result.newCursor != tokens.len():
                panic("Left over tokens (cursor = `result.newCursor`, tokens = `tokens.len()`)")
            # print(result.tree.toDoc().print(80))
            convertParseTree(result.tree)

    # let parser = Parser(file = input, tokens, idx = 0)
    # let decls = match try(parser.spec):
    #     Result.Err(err): panic(errStr(err))
    #     Result.Ok(decls): decls

    # if parser.idx != parser.tokens.len():
    #     panic("Left over tokens")

    let terminalPats: Option[HashMap[Str, Vec[Token]]] = Option.None
    let terminalNames: Vec[Str] = Vec.withCapacity(decls.len())

    for decl: TopDecl in decls.iter():
        match decl:
            TopDecl.Terminals(TerminalsDecl(terminals)):
                if terminalPats is Option.Some(_):
                    panic("Multiple terminals declarations")

                let map: HashMap[Str, Vec[Token]] = HashMap.withCapacity(terminals.len() * 2)
                for terminalDecl: TerminalDecl in terminals.iter():
                    map.insert(terminalDecl.name.substr(1, terminalDecl.name.len() - 1), terminalDecl.pattern)

                terminalPats = Option.Some(map)

            TopDecl.NonTerminal(NonTerminalDecl(name, ..)):
                terminalNames.push(name)

    let terminalPats: HashMap[Str, Vec[Token]] = \
        terminalPats.unwrapOrElse({ panic("Grammar missing terminals declaration") })

    print("# This is generated file, do not edit.")
    print("")
    print("import ParseTree")
    print("import Token")
    print("")

    print(generateNonTerminalType(terminalNames).print(80))
    print("")
    print(generateNonTerminalToStr(terminalNames).print(80))
    print("")
    print(generateNonTerminalEq(terminalNames).print(80))
    print("")

    let nonTerminalDeclIdx = 0
    for decl: TopDecl in decls.iter():
        let nonTerminal = match decl:
            TopDecl.Terminals(_): continue
            TopDecl.NonTerminal(nonTerminal): nonTerminal

        if nonTerminalDeclIdx != 0:
            print("")
        let doc = generateNonTerminal(nonTerminal, terminalPats)
        print(doc.print(80))
        nonTerminalDeclIdx += 1

errStr(err: Error): Str
    "`err.loc.file`:`err.loc.line + 1`:`err.loc.col + 1`: `err.msg`"

capitalize(s: Str): exn Str
    let buf = StrBuf.withCapacity(s.len())
    let chars = s.chars()

    if chars.next[CharIter, Char, exn]() is Option.Some(char):
        buf.push(char.toAsciiUppercase())

    while chars.next() is Option.Some(char):
        buf.push(char)

    buf.toStr()

# --------------------------------------------------------------------------------------------------
# Parsing PEG specs

type Parser:
    file: Str
    tokens: Vec[Token]
    idx: U32

Parser.spec(self): Error Vec[TopDecl]
    let decls: Vec[TopDecl] = Vec.withCapacity(10)
    while self.idx != self.tokens.len():
        decls.push(self.topDecl())
    decls

Parser.topDecl(self): Error TopDecl
    match self.peek():
        Option.Some(Token(kind = TokenKind.UpperId, text = "Terminals", ..)):
            self.idx += 1
            TopDecl.Terminals(self.terminals())

        Option.Some(Token(kind = TokenKind.LowerId, text, ..)):
            self.idx += 1
            TopDecl.NonTerminal(self.nonTerminal(text))

        Option.Some(other):
            throw(Error(loc = self.tokenLoc(other), msg = "Unexpected token `other.kind`"))

        Option.None:
            throw(Error(loc = self.tokenLoc(self.tokens.last().unwrap()), msg = "Unexpected end of file"))

Parser.terminals(self): Error TerminalsDecl
    self.expect(TokenKind.Colon)
    self.expect(TokenKind.Newline)
    self.expect(TokenKind.Indent)

    let terminals: Vec[TerminalDecl] = Vec.withCapacity(10)
    loop:
        let name = self.expect(TokenKind.Str)
        self.expect(TokenKind.Eq)
        let pattern: Vec[Token] = Vec.withCapacity(10)
        while self.peek() is Option.Some(next) && next.kind != TokenKind.Newline:
            pattern.push(next)
            self.idx += 1
        self.expect(TokenKind.Newline)
        terminals.push(TerminalDecl(name = name.text, pattern))

        if self.peek() is Option.Some(Token(kind = TokenKind.Dedent, ..)):
            self.idx += 1
            return TerminalsDecl(terminals)

    panic("Unreachable")

Parser.nonTerminal(self, name: Str): Error NonTerminalDecl
    self.expect(TokenKind.Colon)
    self.expect(TokenKind.Newline)
    self.expect(TokenKind.Indent)

    let alts: Vec[Alt] = Vec.withCapacity(10)
    loop:
        let symbols: Vec[Symbol] = Vec.withCapacity(10)
        while self.peek() is Option.Some(next) && next.kind != TokenKind.Newline:
            symbols.push(self.symbol())
        self.expect(TokenKind.Newline)
        alts.push(Alt(symbols))

        if self.peek() is Option.Some(Token(kind = TokenKind.Dedent, ..)):
            self.idx += 1
            return NonTerminalDecl(name, alts)

    panic("Unreachable")

Parser.symbol(self): Error Symbol
    let next = self.next()

    let ignore = next.kind == TokenKind.Underscore
    let negLookahead = next.kind == TokenKind.Minus

    if ignore || negLookahead:
        next = self.next()

    let symbol = match next.kind:
        TokenKind.LParen:
            let group: Vec[Symbol] = Vec.withCapacity(10)
            while self.peek() is Option.Some(next) && next.kind != TokenKind.RParen:
                group.push(self.symbol())
            self.expect(TokenKind.RParen)
            Symbol.Group(group)

        TokenKind.LowerId:
            Symbol.NonTerminal(next.text)

        TokenKind.Str:
            Symbol.Terminal(next.text.substr(1, next.text.len() - 1))

        other:
            throw(Error(loc = self.tokenLoc(next), msg = "Unexpected token `other`"))

    if self.peek() is Option.Some(next):
        match next.kind:
            TokenKind.Star:
                self.idx += 1
                symbol = Symbol.ZeroOrMore(symbol)

            TokenKind.Plus:
                self.idx += 1
                symbol = Symbol.OneOrMore(symbol)

            TokenKind.Question:
                self.idx += 1
                symbol = Symbol.Optional(symbol)

            _: ()

    if ignore:
        symbol = Symbol.Ignore(symbol)
    elif negLookahead:
        symbol = Symbol.NegLookahead(symbol)

    symbol

Parser.peek(self): Option[Token]
    if self.idx == self.tokens.len():
        return Option.None
    Option.Some(self.tokens.get(self.idx))

Parser.next(self): Error Token
    if self.idx == self.tokens.len():
        throw(Error(loc = self.tokenLoc(self.tokens.last().unwrap()), msg = "Unexpected end of file"))
    let token = self.tokens.get(self.idx)
    self.idx += 1
    token

Parser.expect(self, kind: TokenKind): Error Token
    match self.peek():
        Option.Some(token) if token.kind == kind:
            self.idx += 1
            token

        Option.Some(other):
            throw(Error(loc = self.tokenLoc(other), msg = "Unexpected token `other`, expected `kind`"))

        Option.None:
            throw(Error(loc = self.tokenLoc(self.tokens.last().unwrap()), msg = "Unexpected end of file"))

Parser.tokenLoc(self, token: Token): Loc
    Loc(
        file = self.file,
        byteIdx = token.byteIdx,
        byteLen = token.text.len(),
        line = token.line,
        col = token.col
    )

convertParseTree(tree: ParseTree[Token, NonTerminal]): Vec[TopDecl]
    let topDecls = tree.asNonTerminal(NonTerminal.TopDecls)

    let converted: Vec[TopDecl] = Vec.withCapacity(topDecls.len())

    for topDecl: ParseTree[Token, NonTerminal] in topDecls.iter():
        let topDecl = topDecl.asNonTerminal(NonTerminal.TopDecl).get(0)
        match topDecl:
            ParseTree.NonTerminal(kind = NonTerminal.TerminalsDecl, nodes):
                converted.push(TopDecl.Terminals(convertTerminalsDecl(nodes)))

            ParseTree.NonTerminal(kind = NonTerminal.NonTerminalDecl, nodes):
                converted.push(TopDecl.NonTerminal(convertNonTerminalDecl(nodes)))

            _:
                panic("")

    converted

convertTerminalsDecl(nodes: Vec[ParseTree[Token, NonTerminal]]): TerminalsDecl
    let terminals: Vec[TerminalDecl] = Vec.withCapacity(nodes.len())

    for node: ParseTree[Token, NonTerminal] in nodes.iter():
        let node = node.asNonTerminal(NonTerminal.TerminalDecl)
        let name = node.get(0).asTerminal().text
        let pattern: Vec[Token] = Vec.withCapacity(node.len() - 1)
        for tok: ParseTree[Token, NonTerminal] in node.iter().skip(1):
            pattern.push(tok.asTerminal())
        terminals.push(TerminalDecl(name, pattern))

    TerminalsDecl(terminals)

convertNonTerminalDecl(nodes: Vec[ParseTree[Token, NonTerminal]]): NonTerminalDecl
    let name = nodes.get(0).asTerminal().text

    let alts: Vec[Alt] = Vec.withCapacity(nodes.len() - 1)

    for altTree: ParseTree[Token, NonTerminal] in nodes.iter().skip(1):
        let altTreeNodes = altTree.asNonTerminal(NonTerminal.NonTerminalAlt)
        alts.push(convertAlt(altTreeNodes))

    NonTerminalDecl(name, alts)

convertAlt(nodes: Vec[ParseTree[Token, NonTerminal]]): Alt
    let symbols: Vec[Symbol] = Vec.withCapacity(nodes.len())

    for symbolTree: ParseTree[Token, NonTerminal] in nodes.iter():
        symbols.push(convertSymbol(symbolTree.asNonTerminal(NonTerminal.Symbol)))

    Alt(symbols)

convertSymbol(nodes: Vec[ParseTree[Token, NonTerminal]]): Symbol
    let symbolIdx: U32 = if nodes.get(0) is ParseTree.NonTerminal(kind = NonTerminal.SymbolPrefix, ..):
        1
    else:
        0

    let symbol = convertSymbolNonRec(nodes.get(symbolIdx).asNonTerminal(NonTerminal.SymbolNonRec))

    if nodes.len() > symbolIdx + 1:
        match nodes.get(symbolIdx + 1).asNonTerminal(NonTerminal.SymbolSuffix).get(0).asTerminal().text:
            "*": symbol = Symbol.ZeroOrMore(symbol)
            "+": symbol = Symbol.OneOrMore(symbol)
            "?": symbol = Symbol.Optional(symbol)
            _: panic("")

    if nodes.get(0) is ParseTree.NonTerminal(kind = NonTerminal.SymbolPrefix, nodes):
        match nodes.get(0).asTerminal().text:
            "-": symbol = Symbol.NegLookahead(symbol)
            "_": symbol = Symbol.Ignore(symbol)

    symbol

convertSymbolNonRec(nodes: Vec[ParseTree[Token, NonTerminal]]): Symbol
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

# --------------------------------------------------------------------------------------------------
# Code generation

generateNonTerminalType(nonTerminalNames: Vec[Str]): Doc
    let doc = Doc.str("type NonTerminal:")
    for name: Str in nonTerminalNames.iter():
        doc += Doc.hardLine() + Doc.str(capitalize(name))
    doc.nest(4)

generateNonTerminalToStr(nonTerminalNames: Vec[Str]): Doc
    let doc = Doc.str("impl ToStr[NonTerminal]:")
    doc += Doc.hardLine()

    let fnDoc = Doc.str("toStr(self: NonTerminal): Str")
    fnDoc += Doc.hardLine()

    let matchDoc = Doc.str("match self:")
    for name: Str in nonTerminalNames.iter():
        let capitalName = capitalize(name)
        matchDoc += Doc.hardLine() + Doc.str("NonTerminal.`capitalName`: \"`capitalName`\"")

    (doc + (fnDoc + matchDoc.nest(4)).nest(4)).nest(4)

generateNonTerminalEq(nonTerminalNames: Vec[Str]): Doc
    let doc = Doc.str("impl Eq[NonTerminal]:")
    doc += Doc.hardLine()

    let fnDoc = Doc.str("__eq(self: NonTerminal, other: NonTerminal): Bool")
    fnDoc += Doc.hardLine()

    let matchDoc = Doc.str("match (left = self, right = other):")
    for name: Str in nonTerminalNames.iter():
        let capitalName = capitalize(name)
        matchDoc += Doc.hardLine() + Doc.str("(left = NonTerminal.`capitalName`, right = NonTerminal.`capitalName`): Bool.True")
    matchDoc += Doc.hardLine() + Doc.str("_: Bool.False")

    (doc + (fnDoc + matchDoc.nest(4)).nest(4)).nest(4)

generateNonTerminal(decl: NonTerminalDecl, terminalPats: HashMap[Str, Vec[Token]]): exn Doc
    let doc = Doc.str("`decl.name`(tokens: Vec[Token], cursor: U32): ParseError[Token] (tree: ParseTree[Token, NonTerminal], newCursor: U32)") \
                + Doc.hardLine()

    doc += Doc.str("let cursor0 = cursor") + Doc.hardLine()

    # TODO: Count the non-ignored symbols, allocate vector (or maybe array) with the right size.
    doc += Doc.str("let nodes: Vec[ParseTree[Token, NonTerminal]] = Vec.withCapacity(0)") + Doc.hardLine()

    for alt: Alt in decl.alts.iter():
        let altResultDoc = Doc.str("let altResult = try({") + Doc.hardLine()
        for symbol: Symbol in alt.symbols.iter():
            altResultDoc += generateSymbolParser(symbol, Bool.False, terminalPats) + Doc.hardLine()
        altResultDoc += Doc.str("cursor")
        altResultDoc = altResultDoc.nest(4)
        altResultDoc += Doc.hardLine() + Doc.str("})") + Doc.hardLine()
        doc += altResultDoc

        let altResultMatchDoc = Doc.str("match altResult:") + Doc.hardLine()

        let errAlt = \
            Doc.nested(
                4,
                Doc.str("Result.Err(err):")
                    + Doc.hardLine()
                    + Doc.str("cursor = cursor0")
                    + Doc.hardLine()
                    + Doc.str("nodes.clear()"))

        let okAlt = \
            Doc.nested(
                4,
                Doc.str("Result.Ok(newCursor):")
                    + Doc.hardLine()
                    + Doc.str("return (tree = ParseTree.NonTerminal(kind = NonTerminal.`capitalize(decl.name)`, nodes), newCursor = newCursor)"))

        altResultMatchDoc = Doc.nested(4, altResultMatchDoc + errAlt) + Doc.nested(4, Doc.hardLine() + okAlt)

        doc += altResultMatchDoc + Doc.hardLine()

    let failDoc = \
        Doc.nested(
            4,
            Doc.str("if cursor == tokens.len():")
                + Doc.hardLine()
                + Doc.str("throw(ParseError.UnexpectedEof)"))

    failDoc += Doc.hardLine()
    failDoc += \
        Doc.nested(
            4,
            Doc.str("else:") + Doc.hardLine() + Doc.str("throw(ParseError.UnexpectedToken(tokens.get(cursor)))"))

    doc += failDoc

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
generateSymbolParser(symbol: Symbol, ignore: Bool, terminalPats: HashMap[Str, Vec[Token]]): exn Doc
    match symbol:
        Symbol.Terminal(terminal):
            let patToks = terminalPats.get(terminal).unwrapOrElse({ panic("Unknown terminal: `terminal`") })

            let eofCheck = \
                Doc.nested(
                    4,
                    Doc.str("if cursor == tokens.len():") \
                        + Doc.hardLine() \
                        + Doc.str("throw(ParseError.UnexpectedEof)"))

            eofCheck += Doc.hardLine()

            let tokenKindCheck = Doc.str("if tokens.get(cursor) is ") \
                + tokensToCode(patToks) \
                + Doc.char(':') \
                + Doc.hardLine()

            let nested = Doc.empty()
            if !ignore:
                nested += Doc.str("nodes.push(ParseTree.Terminal(tokens.get(cursor)))") + Doc.hardLine()
            nested += Doc.str("cursor += 1")

            tokenKindCheck = Doc.nested(4, tokenKindCheck + nested) + Doc.hardLine()

            tokenKindCheck += \
                Doc.nested(
                    4,
                    Doc.str("else:")
                        + Doc.hardLine()
                        + Doc.str("throw(ParseError.UnexpectedToken(tokens.get(cursor)))"))

            eofCheck + tokenKindCheck

        Symbol.NonTerminal(nonTerminal):
            let doc = Doc.str("let nonTerminalResult = `nonTerminal`(tokens, cursor)") \
                + Doc.hardLine() \
                + Doc.str("cursor = nonTerminalResult.newCursor")

            if !ignore:
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
            let loopDoc = Doc.str("loop:") + Doc.hardLine()

            let tryDoc = Doc.str("let symResult = try({") + Doc.hardLine()
            tryDoc += generateSymbolParser(symbol, ignore, terminalPats) + Doc.hardLine()
            tryDoc += Doc.str("cursor")
            tryDoc = tryDoc.nest(4)
            tryDoc += Doc.hardLine() + Doc.str("})")

            loopDoc += tryDoc + Doc.hardLine()
            loopDoc += \
                Doc.nested(
                    4,
                    Doc.str("match symResult:")
                        + Doc.hardLine()
                        + Doc.nested(4, Doc.str("Result.Err(_):") + Doc.hardLine() + Doc.str("break"))
                        + Doc.hardLine()
                        + Doc.nested(4, Doc.str("Result.Ok(newCursor):") + Doc.hardLine() + Doc.str("cursor = newCursor")))

            loopDoc.nest(4)

        Symbol.OneOrMore(symbol):
            generateSymbolParser(symbol, ignore, terminalPats) \
                + Doc.hardLine() \
                + generateSymbolParser(Symbol.ZeroOrMore(symbol), ignore, terminalPats)

        Symbol.Optional(symbol):
            let doc = Doc.str("let symResult = try({") + Doc.hardLine()
            doc += generateSymbolParser(symbol, ignore, terminalPats) + Doc.hardLine()
            doc += Doc.str("cursor")
            doc = doc.nest(4)
            doc += Doc.hardLine() + Doc.str("})")

            doc += Doc.hardLine()
            doc += \
                Doc.nested(
                    4,
                    Doc.str("match symResult:")
                        + Doc.hardLine()
                        + Doc.nested(
                            4,
                            Doc.str("Result.Err(_):")
                                + Doc.hardLine()
                                + Doc.str("()"))         # TODO: We will need to truncate the tokens vec here
                        + Doc.hardLine()
                        + Doc.nested(
                                4,
                                Doc.str("Result.Ok(newCursor):")
                                    + Doc.hardLine()
                                    + Doc.str("cursor = newCursor")))

            doc

        Symbol.Ignore(symbol):
            generateSymbolParser(symbol, Bool.True, terminalPats)

        Symbol.NegLookahead(symbol):
            let doc = Doc.str("let tokensLen0 = tokens.len()") + Doc.hardLine()
            doc + Doc.nested(
                4,
                Doc.str("let symResult = try({")
                    + Doc.hardLine()
                    + generateSymbolParser(symbol, Bool.True, terminalPats)) \
                + Doc.hardLine() \
                + Doc.str("})") \
                + Doc.hardLine() \
                + Doc.nested(
                    4,
                    Doc.str("match symResult:")
                        + Doc.hardLine()
                        + Doc.nested(
                            4,
                            Doc.str("Result.Err(_):")
                                + Doc.hardLine()
                                + Doc.str("tokens.truncate(tokensLen0)"))
                        + Doc.hardLine()
                        + Doc.nested(
                            4,
                            Doc.str("Result.Ok(_):")
                                + Doc.hardLine()
                                + Doc.str("throw(ParseError.UnexpectedToken(tokens.get(cursor)))")))

tokensToCode(tokens: Vec[Token]): exn Doc
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
