import Assert
import Lexer
import Token


type ScannerError(
    line: U32,
    col: U32,
    msg: Str,
)


scan(tokens: Vec[Token]) Vec[Token] / [ScannerError, ..exn]:
    let numTokens = tokens.len()

    # Somewhat random: assume an indentation token generated for every 6 tokens.
    # We should tweak this more based on code in the compiler and standard libraries.
    let newTokens = Vec[Token].withCapacity(numTokens + (numTokens / 6))

    let tokenIter = tokens.iter().peekable()

    let firstToken = match peek(tokenIter):
        Option.None: return newTokens
        Option.Some(t): t

    scanIndented(tokenIter, newTokens, firstToken.col)

    # TODO: Make this a debug assertion.
    sanityCheckTokens(newTokens)

    # assert(tokenIter.next().isNone())

    newTokens


## Scan an indented block. Indented blocks start with:
##
## - `:` followed by a token in a new line
## - `{`
##
## In both cases, `blockCol` should be the column number of the first token in the indented block.
## I.e. the column of NOT the `{` but the first non-trivia token after it.
##
## This function does not consume the token terminating the block, i.e. `}` or the dedented token.
scanIndented[Iterator[iter, Token, [ScannerError, ..exn]]](
    tokens: Peekable[iter, Token, [ScannerError, ..exn]],
    newTokens: Vec[Token],
    blockCol: U32,
) / [ScannerError, ..exn]:
    # Don't generate `NEWLINE` before the first token of the block.
    let generateNewline = Bool.False

    while peek(tokens) is Option.Some(t):
        if t.kind is TokenKind.RParen | TokenKind.RBracket | TokenKind.RBrace | TokenKind.Comma:
            if generateNewline and newTokens.last() is Option.Some(tLast):
                newTokens.push(newline(tLast.rightLoc()))
            return

        if newTokens.last() is Option.Some(tLast) and t.line != tLast.line:
            match t.col.cmp(blockCol):
                Ordering.Greater: ()

                Ordering.Equal:
                    if generateNewline:
                        newTokens.push(newline(tLast.rightLoc()))

                Ordering.Less:
                    if generateNewline:
                        newTokens.push(newline(tLast.rightLoc()))
                    return

        generateNewline = Bool.True

        # Consume the peeked token.
        tokens.next[Peekable[iter, Token, [ScannerError, ..exn]], Token, [ScannerError, ..exn]]()
        newTokens.push(t)

        match t.kind:
            TokenKind.LParen | TokenKind.LParenRow:
                scanNonIndented(tokens, newTokens, NonIndentedDelimKind.Paren)

            TokenKind.LBracket | TokenKind.LBracketRow | TokenKind.UpperIdDotLBracket:
                scanNonIndented(tokens, newTokens, NonIndentedDelimKind.Bracket)

            TokenKind.LBrace:
                match peek(tokens):
                    Option.Some(tNext):
                        scanIndented(tokens, newTokens, tNext.col)
                        match next(tokens):
                            Option.Some(t) if t.kind is TokenKind.RBrace:
                                newTokens.push(t)
                            _:
                                throw(~ScannerError(
                                    line = t.line,
                                    col = t.col,
                                    msg = "unterminated '{'"
                                ))
                        generateNewline = Bool.False

                    Option.None:
                        return

            TokenKind.Colon if peek(tokens) is Option.Some(tNext) and tNext.line != t.line:
                # `scanIndented` will generate indentation tokens for the indented block.
                # Generate the wrapping `NEWLINE` + `INDENT` and `DEDENT` here.
                let tRightLoc = t.rightLoc()
                newTokens.push(newline(t.rightLoc()))
                # TODO: We could generate INDENT at the line of the next non-trivia token.
                # I.e. in code like:
                #
                #     do:
                #         # hi
                #         f()
                #
                # Generate it on the line of `f()` instead of `# hi`.
                newTokens.push(indent((line = tRightLoc.line + 1, col = 0)))

                scanIndented(tokens, newTokens, tNext.col)

                # Don't generate `NEWLINE` after a recursive call: the block will end with a
                # `NEWLINE` when it's ends with a non-block, or or it'll end with a `DEDENT`
                # when it ends with a block. In both cases we don't want a `NEWLINE`.
                generateNewline = Bool.False

                let tLast = newTokens.last().unwrap()
                newTokens.push(dedent(tLast.rightLoc()))

            _: ()

    if generateNewline and newTokens.last() is Option.Some(tLast):
        newTokens.push(newline(tLast.rightLoc()))


type NonIndentedDelimKind:
    Paren
    Bracket


## Scan a non-indented block: `(...)` or `[...]`.
##
## Consumes the terminating `)` or `]`.
scanNonIndented[Iterator[iter, Token, [ScannerError, ..exn]]](
    tokens: Peekable[iter, Token, [ScannerError, ..exn]],
    newTokens: Vec[Token],
    delimKind: NonIndentedDelimKind,
) / [ScannerError, ..exn]:
    for t: Token in tokens:
        if t.isTrivia():
            continue

        newTokens.push(t)

        match t.kind:
            TokenKind.RParen:
                match delimKind:
                    NonIndentedDelimKind.Paren:
                        return

                    NonIndentedDelimKind.Bracket:
                        throw(~ScannerError(
                            line = t.line,
                            col = t.col,
                            msg = "')' without matching '('",
                        ))

            TokenKind.RBracket:
                match delimKind:
                    NonIndentedDelimKind.Bracket:
                        return

                    NonIndentedDelimKind.Paren:
                        throw(~ScannerError(
                            line = t.line,
                            col = t.col,
                            msg = "']' without matching '['",
                        ))

            TokenKind.LParen | TokenKind.LParenRow:
                scanNonIndented(tokens, newTokens, NonIndentedDelimKind.Paren)

            TokenKind.LBracket | TokenKind.LBracketRow | TokenKind.UpperIdDotLBracket:
                scanNonIndented(tokens, newTokens, NonIndentedDelimKind.Bracket)

            TokenKind.LBrace:
                let tNext = peek(tokens).unwrap()
                scanIndented(tokens, newTokens, tNext.col)
                match next(tokens):
                    Option.Some(t) if t.kind is TokenKind.RBrace:
                        newTokens.push(t)
                    _:
                        throw(~ScannerError(
                            line = t.line,
                            col = t.col,
                            msg = "unterminated '{'",
                        ))

            TokenKind.RBrace:
                throw(~ScannerError(
                    line = t.line,
                    col = t.col,
                    msg = "'}' without matching '{'",
                ))

            TokenKind.Colon if peek(tokens) is Option.Some(tNext) and tNext.line != t.line:
                # `scanIndented` will generate indentation tokens for the indented block.
                # Generate the wrapping `NEWLINE` + `INDENT` and `DEDENT` here.
                newTokens.push(newline(t.rightLoc()))
                newTokens.push(indent((line = t.rightLoc().line + 1, col = 0)))

                scanIndented(tokens, newTokens, tNext.col)

                # `scanIndented` will stop at a ',', ')', or ']'. Generate `DEDENT` before the
                # next token.
                let lastTokenRight = newTokens.last().unwrap().rightLoc()
                newTokens.push(dedent(lastTokenRight))

            _: ()


peek[Iterator[iter, Token, [ScannerError, ..exn]]](
    tokens: Peekable[iter, Token, [ScannerError, ..exn]]
) Option[Token] / [ScannerError, ..exn]:
    while tokens.peek() is Option.Some(t):
        if t.isTrivia():
            tokens.next[Peekable[iter, Token, [ScannerError, ..exn]], Token, [ScannerError, ..exn]]()
        else:
            return Option.Some(t)

    Option.None


next[Iterator[iter, Token, [ScannerError, ..exn]]](
    tokens: Peekable[iter, Token, [ScannerError, ..exn]]
) Option[Token] / [ScannerError, ..exn]:
    while tokens.next() is Option.Some(t):
        if not t.isTrivia():
            return Option.Some(t)

    Option.None


newline(loc: (line: U32, col: U32)) Token:
    Token(
        kind = TokenKind.Newline,
        text = "",
        byteIdx = 0,
        line = loc.line,
        col = loc.col,
    )


indent(loc: (line: U32, col: U32)) Token:
    Token(
        kind = TokenKind.Indent,
        text = "",
        byteIdx = 0,
        line = loc.line,
        col = loc.col,
    )


dedent(loc: (line: U32, col: U32)) Token:
    Token(
        kind = TokenKind.Dedent,
        text = "",
        byteIdx = 0,
        line = loc.line,
        col = loc.col,
    )


# --------------------------------------------------------------------------------------------------


## Entry point to scan a file print generated tokens.
##
## Used in tests to compare generated tokens with the interpreter's tokens.
scannerDumpTokens(args: Array[Str]) () / []:
    if args.len() != 2:
        panic("USAGE: fir compiler/Scanner.fir --main scannerDumpTokens -- <file>")

    let file = args.get(1)
    let fileContents = readFileUtf8(file)
    let tokens = lexerTokenizeForTesting(file, fileContents)
    let tokens = match try(||: scan[row[]](tokens)):    # Explicitly close the variant (issue #49).
        Result.Err(~ScannerError(line, col, msg)):
            panic("`line + 1`:`col + 1`: `msg`")
        Result.Ok(tokens):
            tokens
    for token: Token in tokens.iter():
        print("`token.line + 1`:`token.col + 1`: `token.kind`")


## Check that tokens are sorted based on line and column.
##
## This mainly checks the comment tokens as that's where things get tricky.
##
## When generating indentation tokens we ignore comments, but we still add them to the tokens as
## tools need comment tokens. This pass makes sure the comment tokens are added at the right places.
sanityCheckTokens(tokens: Vec[Token]):
    if tokens.isEmpty():
        return

    for i: U32 in range(u32(2), tokens.len()):
        let t0 = tokens.get(i - 1)
        let t1 = tokens.get(i)

        # Note: indentation tokens are generated at the same location
        let ok = t0.line < t1.line or (t0.line == t1.line and t0.col <= t1.col)

        if not ok:
            panic("Token at index `i-1`=`t0`, index `i`=`t1`")
