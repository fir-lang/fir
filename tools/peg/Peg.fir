import Compiler.Assert
import Compiler.Lexer
import Compiler.Scanner
import Compiler.Token
import ParseTree
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
        Result.Err(ParseError(cursor)):
            if cursor == tokens.len():
                panic("Unexpected end of input")
            else:
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
        # If the non-terminal has a return type, then it needs to have a semantic action, and we
        # don't generate a constructor for the non-terminal in the parse tree types, as we never
        # allocate it.
        if nonTerminal.ty.isSome():
            # Check that all productions have a semantic action.
            for alt: Alt in nonTerminal.alts.iter():
                if alt.rhs.isNone():
                    panic("Non-terminal `nonTerminal.name` has a return type, but it also has production(s) without a semantic action.")

            # Don't generate a constructor for it.
            continue

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

    let altIdx: U32 = 1

    let ty: Option[Vec[ParseTree[Token, NonTerminal]]] = Option.None
    if nodes.get(1) is ParseTree.NonTerminal(kind = NonTerminal.Type_, nodes):
        altIdx += 1
        ty = Option.Some(nodes)

    let alts: Vec[Alt] = Vec.withCapacity(nodes.len() - altIdx)

    for altTree: ParseTree[Token, NonTerminal] in nodes.iter().skip(altIdx):
        let altTreeNodes = altTree.asNonTerminal(NonTerminal.NonTerminalAlt)
        alts.push(convertAlt(altTreeNodes))

    NonTerminalDecl(name, ty, alts)

convertAlt(nodes: Vec[ParseTree[Token, NonTerminal]]) Alt:
    let symbols: Vec[Symbol] = Vec.withCapacity(nodes.len())

    for symbolTree: ParseTree[Token, NonTerminal] in nodes.iter():
        if symbolTree is ParseTree.NonTerminal(kind = NonTerminal.NonTerminalRhs, nodes = rhsNodes):
            if rhsNodes.isEmpty():
                return Alt(symbols, rhs = Option.None)
            else:
                # print("-------")
                # print(symbolTree.toDoc().render(80))
                # print("-------")
                return Alt(symbols, rhs = Option.Some(rhsNodes))

        symbols.push(convertSymbol(symbolTree.asNonTerminal(NonTerminal.Symbol)))

    Alt(symbols, rhs = Option.None)

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
        match nodes.get(0).asTerminal():
            Token(kind = TokenKind.Minus, ..):
                symbol = Symbol.NegLookahead(symbol)

            Token(kind = TokenKind.Underscore, ..):
                symbol = Symbol.Ignore(symbol)

            Token(kind = TokenKind.LowerId, text = binder, ..):
                symbol = Symbol.Bind(binder, symbol)

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

    ## Optional return type of the non-terminal, as a token tree.
    ty: Option[Vec[ParseTree[Token, NonTerminal]]]

    alts: Vec[Alt]

## Alternatives of a non-terminal.
type Alt:
    symbols: Vec[Symbol]

    ## Optional semantic action of the production, as a token tree.
    rhs: Option[Vec[ParseTree[Token, NonTerminal]]]

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

    ## Binder: `x=symbol`. Binds the result of parsing `symbol` to variable `x`, to be used in the
    ## semantic action of the production.
    Bind(Str, Symbol)

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
    let returnTy = match decl.ty:
        Option.Some(ty):
            Doc.str(generateType(ty))
        Option.None:
            Doc.str("ParseTree[`terminalType`, `nonTerminalType`]")

    let doc = Doc.str("`decl.name`(tokens: Vec[`terminalType`], cursor: U32) (tree: ")
                + returnTy
                + Doc.str(", newCursor: U32, newErr: Option[ParseError]) / ParseError:")
                + Doc.hardLine()

    doc += Doc.str("let cursor0 = cursor") + Doc.hardLine()
    doc += Doc.str("let curErr: Option[ParseError] = Option.None") + Doc.hardLine()

    for alt: Alt in decl.alts.iter():
        let altResultDoc = Doc.str("let altResult = try(||:") + Doc.hardLine()

        # if alt.rhs.isNone():
        # TODO: Count the non-ignored symbols, allocate vector (or maybe array) with the right size.
        # TODO: Update the symbol code generator to only push to `nodes` when the production doesn't
        # have a semantic action, then move this code to the commented-out `if` above.
        altResultDoc += Doc.str("let nodes: Vec[ParseTree[`terminalType`, `nonTerminalType`]] = Vec.empty()") + Doc.hardLine()

        let symbolCont = if alt.rhs.isSome():
            SymbolCont.Ignore
        else:
            SymbolCont.PushToParseTree("nodes")

        for symbol: Symbol in alt.symbols.iter():
            altResultDoc += generateSymbolParser(symbol, terminalPats, symbolCont) + Doc.hardLine()

        let valueDoc = match alt.rhs:
            Option.None:
                Doc.str("ParseTree.NonTerminal(kind = `nonTerminalType`.`capitalize(decl.name)`, nodes)")
            Option.Some(semanticActionTokens):
                let tokens = Vec.withCapacity(50)
                for node: ParseTree[Token, NonTerminal] in semanticActionTokens.iter():
                    parseTreeTokens(node, tokens)
                let code = tokensToCode(tokens)
                let lines: Vec[Str] = code.lines().toVec()
                let doc = Doc.empty()
                let lineIdx: U32 = 0
                for line in lines.iter():
                    if lineIdx != 0:
                        doc += Doc.hardLine()
                    doc += Doc.str(line)
                    lineIdx += 1
                doc

        altResultDoc +=
            Doc.nested(4, Doc.str("let value = do:") + Doc.hardLine() + valueDoc)

        altResultDoc += Doc.hardLine()

        altResultDoc += Doc.str("(value = value, cursor = cursor, err = curErr)")

        altResultDoc = altResultDoc.nest(4)

        # Terminate `try(||: ...)`.
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
                    + Doc.str("cursor = cursor0"))

        let okAlt =
            Doc.nested(
                4,
                Doc.str("Result.Ok((value = value, cursor = newCursor, err = newErr)):")
                    + Doc.hardLine()
                    + Doc.str("return (tree = value, newCursor = newCursor, newErr = newErr)"))

        altResultMatchDoc = Doc.nested(4, altResultMatchDoc + errAlt) + Doc.nested(4, Doc.hardLine() + okAlt)

        doc += altResultMatchDoc + Doc.hardLine()

    doc += makeThrow(makeUnexpectedTokenError())

    doc.nest(4)


## What to do with a symbol value.
type SymbolCont:
    ## Bind the symbol value to the variable.
    Bind(Str)

    ## Push the symbol value to the vector in the variable.
    Push(Str)

    ## Push the symbol value to the vector in the variable.
    ##
    ## Difference from `SymbolCont.Push` is that this pushes values of group symbols.
    PushToParseTree(Str)

    ## Ignore the symbol value.
    Ignore

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
generateSymbolParser(
    symbol: Symbol,
    terminalPats: HashMap[Str, Vec[Token]],
    cont: SymbolCont,
) Doc / exn:
    match symbol:
        Symbol.Terminal(terminal):
            let patToks = terminalPats.get(terminal).unwrapOrElse(||: panic("Unknown terminal: `terminal`"))

            let doc = Doc.empty()

            if cont is SymbolCont.Bind(local):
                doc += Doc.str("let `local` = ")

            let tokenKindCheck = Doc.str("if tokens.getOpt(cursor) is Option.Some(")
                + Doc.str(tokensToCode(patToks))
                + Doc.str("):")
                + Doc.hardLine()

            let nested = match cont:
                SymbolCont.Bind(local):
                    Doc.str("let sym = tokens.get(cursor)")
                        + Doc.hardLine()
                        + Doc.str("cursor += 1")
                        + Doc.hardLine()
                        + Doc.str("sym")

                SymbolCont.Push(vecLocal):
                    Doc.str("`vecLocal`.push(tokens.get(cursor))")
                        + Doc.hardLine()
                        + Doc.str("cursor += 1")

                SymbolCont.PushToParseTree(vecLocal):
                    Doc.str("`vecLocal`.push(ParseTree.Terminal(tokens.get(cursor)))")
                        + Doc.hardLine()
                        + Doc.str("cursor += 1")

                SymbolCont.Ignore:
                    Doc.str("cursor += 1")

            tokenKindCheck = Doc.nested(4, tokenKindCheck + nested) + Doc.hardLine()

            doc + tokenKindCheck +
                Doc.nested(
                    4,
                    Doc.str("else:")
                        + Doc.hardLine()
                        + makeThrow(makeUnexpectedTokenError()))

        Symbol.NonTerminal(nonTerminal):
            let doc = Doc.str("let nonTerminalResult = `nonTerminal`(tokens, cursor)")
                + Doc.hardLine()
                + Doc.str("cursor = nonTerminalResult.newCursor")
                + Doc.hardLine()
                + Doc.str("curErr = nonTerminalResult.newErr")

            match cont:
                SymbolCont.Bind(local):
                    doc += Doc.hardLine() + Doc.str("let `local` = nonTerminalResult.tree")

                SymbolCont.Push(vecLocal) | SymbolCont.PushToParseTree(vecLocal):
                    doc += Doc.hardLine() + Doc.str("`vecLocal`.push(nonTerminalResult.tree)")

                SymbolCont.Ignore:
                    ()

            doc

        Symbol.Group(symbols):
            let doc = Doc.empty()

            let symIdx: U32 = 0
            for symbol: Symbol in symbols.iter():
                if symIdx != 0:
                    doc += Doc.hardLine()

                let symbolCont = match cont:
                    SymbolCont.Bind(_) | SymbolCont.Push(_) | SymbolCont.Ignore:
                        # Ignore by default. Named symbols will be returned in a record.
                        SymbolCont.Ignore

                    SymbolCont.PushToParseTree(vecLocal):
                        SymbolCont.PushToParseTree(vecLocal)

                doc += generateSymbolParser(symbol, terminalPats, symbolCont)

                symIdx += 1

            if not (cont is SymbolCont.Ignore):
                let recordNames: Vec[Str] = Vec.withCapacity(symbols.len())
                for symbol: Symbol in symbols.iter():
                    if symbol is Symbol.Bind(name, _):
                        recordNames.push(name)

                let recordDoc = Doc.char('(')
                let nameIdx: U32 = 0
                for name: Str in recordNames.iter():
                    if nameIdx != 0:
                        recordDoc += Doc.str(", ")
                    recordDoc += Doc.str(name) + Doc.str(" = ") + Doc.str(name)
                    nameIdx += 1
                recordDoc += Doc.char(')')

                match cont:
                    SymbolCont.Bind(local):
                        doc += Doc.hardLine() + Doc.str("let `local` = ") + recordDoc

                    SymbolCont.Push(vecLocal):
                        doc += Doc.hardLine() + Doc.str("`vecLocal`.push(") + recordDoc + Doc.char(')')

                    SymbolCont.PushToParseTree(_):
                        # Already handled by the symbols.
                        ()

                    SymbolCont.Ignore:
                        # Checked above in the conditional.
                        panic("")

            doc

        Symbol.ZeroOrMore(symbol):
            let doc = Doc.empty()

            let symbolCont = match cont:
                SymbolCont.Bind(local):
                    # `x = symbol*`
                    doc += Doc.str("let `local` = Vec.empty()") + Doc.hardLine()
                    SymbolCont.Push(local)

                SymbolCont.Push(local):
                    # I think this can only happen in strange symbols like `symbol**`.
                    # For now ignore this case.
                    panic("")

                SymbolCont.PushToParseTree(local):
                    # `symbol*` without a binder and semantic action.
                    SymbolCont.PushToParseTree(local)

                SymbolCont.Ignore:
                    # `_"foo"*`.
                    SymbolCont.Ignore

            doc += Doc.nested(
                4,
                Doc.str("loop:")
                    + Doc.hardLine()
                    + Doc.str("let nodesLen0 = nodes.len()")
                    + Doc.hardLine()
                    + Doc.nested(
                        4,
                        Doc.str("let symResult = try(||:")
                            + Doc.hardLine()
                            + generateSymbolParser(symbol, terminalPats, symbolCont)
                            + Doc.hardLine()
                            + Doc.str("(cursor = cursor, err = curErr)"))
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
                                Doc.str("Result.Ok(ok):")
                                    + Doc.hardLine()
                                    + Doc.str("cursor = ok.cursor")
                                    + Doc.hardLine()
                                    + Doc.str("curErr = ParseError.takeAdvancedOpt(curErr, ok.err)"))))

            doc

        Symbol.OneOrMore(symbol):
            let doc = Doc.empty()

            # Same as ZeroOrMore case above.
            let symbolCont = match cont:
                SymbolCont.Bind(local):
                    # `x = symbol*`
                    doc += Doc.str("let `local` = Vec.empty()") + Doc.hardLine()
                    SymbolCont.Push(local)

                SymbolCont.Push(local):
                    # I think this can only happen in strange symbols like `symbol**`.
                    # For now ignore this case.
                    panic("")

                SymbolCont.PushToParseTree(local):
                    # `symbol*` without a binder and semantic action.
                    SymbolCont.PushToParseTree(local)

                SymbolCont.Ignore:
                    # `_"foo"*`.
                    SymbolCont.Ignore

            doc + generateSymbolParser(symbol, terminalPats, cont)
                + Doc.hardLine()
                + generateSymbolParser(Symbol.ZeroOrMore(symbol), terminalPats, cont)

        Symbol.Optional(symbol):
            let optionalRecordDoc = match cont:
                SymbolCont.Bind(local):
                    Doc.str("(cursor = cursor, err = curErr, val = `local`)")

                SymbolCont.Push(_) | SymbolCont.PushToParseTree(_) | SymbolCont.Ignore:
                    # Symbol parser directly pushes to the vectors, or ignores.
                    Doc.str("(cursor = cursor, err = curErr)")

            let optionalOkDoc =
                Doc.str("cursor = ok.cursor")
                    + Doc.hardLine()
                    + Doc.str("curErr = ParseError.takeAdvancedOpt(curErr, ok.err)")

            let optionalErrDoc =
                makeUpdateError() + Doc.hardLine() + Doc.str("nodes.truncate(nodesLen0)")

            let symResultBinder = Doc.empty()

            if cont is SymbolCont.Bind(local):
                optionalOkDoc += Doc.hardLine() + Doc.str("Option.Some(ok.val)")
                optionalErrDoc += Doc.hardLine() + Doc.str("Option.None")
                symResultBinder += Doc.str("let `local` = ")

            Doc.str("let nodesLen0 = nodes.len()")
                + Doc.hardLine()
                + Doc.nested(
                      4,
                      Doc.str("let symResult = try(||:")
                          + Doc.hardLine()
                          + generateSymbolParser(symbol, terminalPats, cont)
                          + Doc.hardLine()
                          + optionalRecordDoc)
                 + Doc.hardLine()
                 + Doc.str(")")
                 + Doc.hardLine()
                 + Doc.nested(
                       4,
                       symResultBinder
                           + Doc.str("match symResult:")
                           + Doc.hardLine()
                           + Doc.nested(
                               4,
                               Doc.str("Result.Err(err):")
                                   + Doc.hardLine()
                                   + optionalErrDoc)
                           + Doc.hardLine()
                           + Doc.nested(
                                   4,
                                   Doc.str("Result.Ok(ok):")
                                       + Doc.hardLine()
                                       + optionalOkDoc))

        Symbol.Ignore(symbol):
            generateSymbolParser(symbol, terminalPats, SymbolCont.Ignore)

        Symbol.NegLookahead(symbol):
            let doc = Doc.str("let tokensLen0 = tokens.len()") + Doc.hardLine()
            doc + Doc.nested(
                4,
                Doc.str("let symResult = try(||:")
                    + Doc.hardLine()
                    + generateSymbolParser(symbol, terminalPats, SymbolCont.Ignore))
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
                                + makeThrow(makeUnexpectedTokenError())))

        Symbol.Bind(binder, symbol):
            generateSymbolParser(symbol, terminalPats, SymbolCont.Bind(binder))

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
                        + makeThrow(makeUnexpectedTokenError()))


tokensToCode(tokens: Vec[Token]) Str / exn:
    if tokens.len() == 0:
        return ""

    let out = StrBuf.withCapacity(100)

    let lastLine = tokens.get(0).line
    let lastCol = tokens.get(0).col

    let col0 = lastCol

    for token: Token in tokens.iter():
        if token.line != lastLine:
            out.push('\n')
            lastCol = col0
            lastLine = token.line

        while lastCol < token.col:
            out.push(' ')
            lastCol += 1

        out.pushStr(token.text)

        # TODO: We could iterate the text once, increment column and push chars.
        lastCol += token.text.chars().count[CharIter, Char, exn]()

    out.toStr()

makeUnexpectedTokenError() Doc:
    Doc.str("ParseError.takeAdvanced(curErr, ParseError(cursor = cursor))")

makeThrow(expr: Doc) Doc:
    Doc.nested(4, Doc.str("throw(") + Doc.break_(0) + expr + Doc.char(')')).group()

# When generating code that backtracks, update the local `curErr: Option[ParseError]` if the new
# error's cursor is more advanced than the current.
#
# The new error value should be named `err`.
makeUpdateError() Doc:
    Doc.str("curErr = Option.Some(ParseError.takeAdvanced(curErr, err))")

generateType(nodes: Vec[ParseTree[Token, NonTerminal]]) Str:
    let tokens: Vec[Token] = Vec.withCapacity(4)
        # Size of a generic type with one argument, e.g. `Option[U32]`.

    for node: ParseTree[Token, NonTerminal] in nodes.iter():
        parseTreeTokens(node, tokens)

    tokensToCode(tokens)

parseTreeTokens(tree: ParseTree[t, nt], tokens: Vec[t]):
    match tree:
        ParseTree.Terminal(t):
            tokens.push(t)

        ParseTree.NonTerminal(nodes, ..):
            for node: ParseTree[t, nt] in nodes.iter():
                parseTreeTokens(node, tokens)
