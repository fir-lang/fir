import Assert
import Lexer
import Token


type ScannerError:
    line: U32
    col: U32
    msg: Str


scan(tokens: Vec[Token]) Vec[Token] / [ScannerError, ..exn]:
    if tokens.len() == 0:
        return tokens

    let numTokens = tokens.len()

    # Somewhat random: assume an indentation token generated for every 6 tokens.
    # We should tweak this more based on code in the compiler and standard libraries.
    let newTokens = Vec[Token].withCapacity(numTokens + (numTokens / 6))

    scanIndented(
        tokens.iter().peekable(),
        newTokens,
        (line = u32(0), col = u32(0)),
        IndentedDelimKind.File,
        Option.None,
    )

    newTokens


type IndentedDelimKind:
    Brace
    Bracket
    File
    Paren


IndentedDelimKind.openingDelim(self) Char:
    match self:
        IndentedDelimKind.File: panic("")
        IndentedDelimKind.Brace: '{'
        IndentedDelimKind.Paren: '('
        IndentedDelimKind.Bracket: '['


IndentedDelimKind.terminate(self, token: TokenKind) Bool:
    match self:
        IndentedDelimKind.File: Bool.False
        IndentedDelimKind.Brace: token is TokenKind.RBrace
        IndentedDelimKind.Paren: token is TokenKind.RParen | TokenKind.Comma
        IndentedDelimKind.Bracket: token is TokenKind.RBracket | TokenKind.Comma


scanIndented[Iterator[iter, Token, [ScannerError, ..exn]]](
    tokens: Peekable[iter, Token, [ScannerError, ..exn]],
    newTokens: Vec[Token],
    ldelimLoc: (line: U32, col: U32),
    delimKind: IndentedDelimKind,
    lastLoc: Option[(line: U32, col: U32)]
) (line: U32, col: U32) / [ScannerError, ..exn]:
    if tokens.peek().isNone():
        match delimKind:
            IndentedDelimKind.File:
                return (line = 0, col = 0)
            IndentedDelimKind.Brace | IndentedDelimKind.Paren | IndentedDelimKind.Bracket:
                throw(~ScannerError(
                    line = ldelimLoc.line,
                    col = ldelimLoc.col,
                    msg = "unterminated '`delimKind.openingDelim()`'"
                ))

    let generateIndent = lastLoc.isSome()

    let lastLoc: (line: U32, col: U32) = lastLoc.unwrapOrElse(||:
        let tok = tokens.peek().unwrap()
        (line = tok.line, col = tok.col))

    let indentStack: Vec[U32] = Vec.[lastLoc.col]

    for t: Token in tokens:
        let l = (line = t.line, col = t.col)

        if delimKind.terminate(t.kind):
            # Terminate the last statement.
            if not (newTokens.last() is Option.Some(Token(kind = TokenKind.Newline, ..))):
                newTokens.push(newline(lastLoc))

            # Terminate open blocks.
            # Note that because we don't generate an `INDENT` after `{`, we shouldn't generate a
            # `DEDENT` for top indentation level.
            while indentStack.len() > 1:
                indentStack.pop()
                newTokens.push(dedent(l))

            # Push the token terminating the indented block.
            newTokens.push(t)

            return l

        if l.line != lastLoc.line:
            # Generate indentation tokens.
            let lastIndent = indentStack.last().unwrap()
            match l.col.cmp(lastIndent):
                Ordering.Greater:
                    if generateIndent:
                        indentStack.push(l.col)
                        newTokens.push(newline(lastLoc))
                        newTokens.push(indent((line = lastLoc.line + 1, col = 0)))

                Ordering.Equal:
                    # Generate a newline at the last line.
                    newTokens.push(newline(lastLoc))

                Ordering.Less:
                    newTokens.push(newline(lastLoc))
                    loop:
                        indentStack.pop()
                        newTokens.push(dedent(lastLoc))
                        if indentStack.last() is Option.Some(next):
                            if l.col >= next:
                                break
                        else:
                            break

        lastLoc = t.rightLoc()

        newTokens.push(t)

        generateIndent = Bool.False

        match t.kind:
            TokenKind.LParen | TokenKind.LParenRow:
                lastLoc = scanNonIndented(tokens, newTokens, l, NonIndentedDelimKind.Paren)

            TokenKind.LBracket | TokenKind.LBracketRow | TokenKind.UpperIdDotLBracket:
                lastLoc = scanNonIndented(tokens, newTokens, l, NonIndentedDelimKind.Bracket)

            TokenKind.LBrace:
                lastLoc = scanIndented(tokens, newTokens, l, IndentedDelimKind.Brace, Option.None)

            TokenKind.RParen:
                throw(~ScannerError(
                    line = l.line,
                    col = l.col,
                    msg = "')' without matching '('"
                ))

            TokenKind.RBracket:
                throw(~ScannerError(
                    line = l.line,
                    col = l.col,
                    msg = "']' without matching '['"
                ))

            TokenKind.RBrace:
                throw(~ScannerError(
                    line = l.line,
                    col = l.col,
                    msg = "'}' without matching '{'"
                ))

            TokenKind.Colon:
                generateIndent = Bool.True

            _: ()

    # When scanning a file we won't see a token that termintes the block, the loop will terminate
    # instead to indicate "EOF". Generate DEDENTs as usual.
    newTokens.push(newline(lastLoc))
    while indentStack.len() > 1:
        indentStack.pop()
        newTokens.push(dedent(lastLoc))

    lastLoc


type NonIndentedDelimKind:
    Paren
    Bracket


scanNonIndented[Iterator[iter, Token, [ScannerError, ..exn]]](
    tokens: Peekable[iter, Token, [ScannerError, ..exn]],
    newTokens: Vec[Token],
    ldelimLoc: (line: U32, col: U32),
    delimKind: NonIndentedDelimKind,
) (line: U32, col: U32) / [ScannerError, ..exn]:
    let lastLoc = ldelimLoc

    for t: Token in tokens:
        lastLoc = t.rightLoc()
        let l = lastLoc

        newTokens.push(t)

        match t.kind:
            TokenKind.RParen:
                match delimKind:
                    NonIndentedDelimKind.Paren:
                        return lastLoc

                    NonIndentedDelimKind.Bracket:
                        throw(~ScannerError(
                            line = l.line,
                            col = l.col,
                            msg = "')' without matching '('",
                        ))

            TokenKind.RBracket:
                match delimKind:
                    NonIndentedDelimKind.Bracket:
                        return lastLoc

                    NonIndentedDelimKind.Paren:
                        throw(~ScannerError(
                            line = t.line,
                            col = t.col,
                            msg = "']' without matching '['",
                        ))

            TokenKind.LParen | TokenKind.LParenRow:
                lastLoc = scanNonIndented(tokens, newTokens, l, NonIndentedDelimKind.Paren)

            TokenKind.LBracket | TokenKind.LBracketRow | TokenKind.UpperIdDotLBracket:
                lastLoc = scanNonIndented(tokens, newTokens, l, NonIndentedDelimKind.Bracket)

            TokenKind.LBrace:
                lastLoc = scanIndented(tokens, newTokens, l, IndentedDelimKind.Brace, Option.None)

            TokenKind.RBrace:
                throw(~ScannerError(
                    line = l.line,
                    col = l.col,
                    msg = "'}' without matching '{'",
                ))

            TokenKind.Colon if tokens.peek() is Option.Some(tNext) and tNext.line != lastLoc.line:
                lastLoc = scanIndented(
                    tokens,
                    newTokens,
                    # Position of the colon so that scanIndented will generate NEWLINE and INDENT.
                    lastLoc,
                    match delimKind:
                        NonIndentedDelimKind.Paren: IndentedDelimKind.Paren
                        NonIndentedDelimKind.Bracket: IndentedDelimKind.Bracket,
                    # Somewhat hacky: pass column 0 so that we consider the next line as indented
                    # even if it's dedented.
                    Option.Some((
                        line = lastLoc.line,
                        col = 0,
                    )),
                )
                match newTokens.last().unwrap().kind:
                    TokenKind.Comma:
                        continue
                    TokenKind.RParen:
                        # assertEq(delimKind, NonIndentedDelimKind.Paren)
                        break
                    TokenKind.RBracket:
                        # assertEq(delimKind, NonIndentedDelimKind.Bracket)
                        break
                    other:
                        throw(~ScannerError(
                            line = l.line,
                            col = l.col,
                            msg = "':' after `other`",
                        ))

            _: ()

    lastLoc


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
