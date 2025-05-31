import Token
import Lexer

scan(tokens: Vec[Token]): Vec[Token]
    if tokens.len() == 0:
        return tokens

    # Somewhat random: assume an indentation token generated for every 6 tokens.
    # We should tweak this more based on code in the compiler and standard libraries.
    let newTokens: Vec[Token] = Vec.withCapacity(tokens.len() + tokens.len() / 6)

    # NB. This stack should never be empty.
    let indentStack: Vec[U32] = Vec.withCapacity(10)
    indentStack.push(0)

    let lastLine = tokens.get(0).line
    let lastCol = tokens.get(0).col
    let lastByteIdx = tokens.get(0).byteIdx

    let delimiterStack: Vec[Delimiter] = Vec.withCapacity(10)

    let skipIndent = Bool.False

    for token: Token in tokens.iter():
        let tokenKind = token.kind

        if tokenKind is TokenKind.Backslash:
            skipIndent = Bool.True
            continue

        if delimiterStack.last() is Option.None | Option.Some(Delimiter.Brace) \
                && token.line != lastLine \
                && !skipIndent:
            # Generate a newline at the last line.
            newTokens.push(Token(
                kind = TokenKind.Newline,
                text = "\n",
                byteIdx = lastByteIdx,
                line = lastLine,
                col = lastCol
            ))

            # Generate indentation tokens.
            loop:
                let lastIndent = indentStack.last().unwrapOrElse({ panic("Indent stack is empty") })
                match token.col.cmp(lastIndent):
                    Ordering.Greater:
                        indentStack.push(token.col)
                        newTokens.push(Token(
                            kind = TokenKind.Indent,
                            text = "\t",
                            byteIdx = token.byteIdx,
                            line = token.line,
                            col = token.col
                        ))
                        break

                    Ordering.Equal: break

                    Ordering.Less:
                        indentStack.pop()
                        newTokens.push(Token(
                            kind = TokenKind.Dedent,
                            text = "",
                            byteIdx = token.byteIdx,
                            line = token.line,
                            col = token.col,
                        ))

        lastLine = token.line
        lastCol = token.col
        lastByteIdx = token.byteIdx

        match token.kind:
            TokenKind.LParen: delimiterStack.push(Delimiter.Paren)

            TokenKind.LBracket: delimiterStack.push(Delimiter.Bracket)

            TokenKind.LBrace: delimiterStack.push(Delimiter.Brace)

            TokenKind.RParen:
                if !(delimiterStack.pop() is Option.Some(Delimiter.Paren)):
                    panic("")

            TokenKind.RBracket:
                if !(delimiterStack.pop() is Option.Some(Delimiter.Bracket)):
                    panic("")

            TokenKind.RBrace:
                if !(delimiterStack.pop() is Option.Some(Delimiter.Brace)):
                    panic("")

            _: ()

        newTokens.push(token)
        skipIndent = Bool.False

    # Python 3 seems to always generate a NEWLINE at the end before DEDENTs, even when the line
    # doesn't have a '\n' at the end, probably to terminate the last statement?
    let lastTok = newTokens.last().unwrap()
    newTokens.push(Token(
        kind = TokenKind.Newline,
        text = "\n",
        byteIdx = lastTok.byteIdx,
        line = lastTok.line,
        col = lastTok.col,
    ))

    # Terminate open blocks at the end.
    while indentStack.pop() is Option.Some(indent):
        if indent == 0:
            # TODO: Make this an ssertion
            if indentStack.len() != 0:
                panic("")
            break

        newTokens.push(Token(
            kind = TokenKind.Dedent,
            text = "",
            byteIdx = lastTok.byteIdx,
            line = lastTok.line,
            col = lastTok.col,
        ))

    newTokens

type Delimiter:
    Paren
    Bracket
    Brace

# --------------------------------------------------------------------------------------------------

scannerTests(): [] ()
    let expected: Vec[TokenKind] = Vec.withCapacity(10)
    expected.push(TokenKind.LowerId) # a
    expected.push(TokenKind.Newline)
    expected.push(TokenKind.Indent)
    expected.push(TokenKind.LowerId) # b
    expected.push(TokenKind.Newline)
    expected.push(TokenKind.LowerId) # c
    expected.push(TokenKind.Newline)
    expected.push(TokenKind.Dedent)
    expected.push(TokenKind.LowerId) # d
    expected.push(TokenKind.Newline)
    _scanTest(
        "Indent simple - 1",
        "\
a
    b
    c
d", expected)

    expected.clear()
    expected.push(TokenKind.LowerId) # a
    expected.push(TokenKind.Newline)
    expected.push(TokenKind.Indent)
    expected.push(TokenKind.LowerId) # b
    expected.push(TokenKind.Newline)
    expected.push(TokenKind.Indent)
    expected.push(TokenKind.LowerId) # c
    expected.push(TokenKind.Newline)
    expected.push(TokenKind.Dedent)
    expected.push(TokenKind.Dedent)
    expected.push(TokenKind.LowerId) # d
    expected.push(TokenKind.Newline)
    _scanTest(
        "Indent simple - 2",
        "\
a
    b
        c
d", expected)

    expected.clear()
    expected.push(TokenKind.LowerId) # a
    expected.push(TokenKind.Newline)
    expected.push(TokenKind.Indent)
    expected.push(TokenKind.LowerId) # b
    expected.push(TokenKind.Newline)
    expected.push(TokenKind.Indent)
    expected.push(TokenKind.LowerId) # c
    expected.push(TokenKind.Newline)
    expected.push(TokenKind.Dedent)
    expected.push(TokenKind.Dedent)
    _scanTest(
        "Dedent at the end",
        "\
a
    b
        c", expected)

    expected.clear()
    expected.push(TokenKind.If)
    expected.push(TokenKind.UpperId)
    expected.push(TokenKind.Colon)
    expected.push(TokenKind.Newline)
    expected.push(TokenKind.Indent)
    expected.push(TokenKind.LowerId)
    expected.push(TokenKind.LParen)
    expected.push(TokenKind.LowerId)
    expected.push(TokenKind.LParen)
    expected.push(TokenKind.LowerId)
    expected.push(TokenKind.Comma)
    expected.push(TokenKind.LowerId)
    expected.push(TokenKind.Comma)
    expected.push(TokenKind.LowerId)
    expected.push(TokenKind.RParen)
    expected.push(TokenKind.Comma)
    expected.push(TokenKind.LowerId)
    expected.push(TokenKind.Comma)
    expected.push(TokenKind.LowerId)
    expected.push(TokenKind.RParen)
    expected.push(TokenKind.Newline)
    expected.push(TokenKind.Dedent)
    expected.push(TokenKind.LowerId)
    expected.push(TokenKind.Newline)
    _scanTest(
        "Line joining in parens",
        "\
if True:
    test(test(
                a,
            b,
c),
x, y)
z", expected)

    expected.clear()
    expected.push(TokenKind.Fn_)
    expected.push(TokenKind.LParen)
    expected.push(TokenKind.RParen)
    expected.push(TokenKind.LBrace)
    expected.push(TokenKind.Newline)
    expected.push(TokenKind.Indent)
    expected.push(TokenKind.LowerId) # a
    expected.push(TokenKind.Newline)
    expected.push(TokenKind.LowerId) #b
    expected.push(TokenKind.Newline)
    expected.push(TokenKind.Dedent)
    expected.push(TokenKind.RBrace)
    expected.push(TokenKind.Newline)
    _scanTest(
        "Braces",
        "\
fn() {
    a
    b
}", expected)

    expected.clear()
    expected.push(TokenKind.LowerId)
    expected.push(TokenKind.Colon)
    expected.push(TokenKind.Newline)
    expected.push(TokenKind.Indent)
    expected.push(TokenKind.LowerId)
    expected.push(TokenKind.Newline)
    expected.push(TokenKind.LowerId)
    expected.push(TokenKind.Newline)
    expected.push(TokenKind.Dedent)

    _scanTest(
        "Layout tokens after comments",
        "\
symbolNonRec:
    a  # foo
    b  # bar", expected)

_scanTest(testName: Str, input: Str, expected: Vec[TokenKind])
    printNoNl(testName)

    let (tokens, error) = tokenize("Test.fir", input)

    if error is Option.Some(error):
        print("\t\tLexer error: `error.msg`")
        return

    let tokens = scan(tokens)
    let tokenKinds: Vec[TokenKind] = Vec.withCapacity(tokens.len())
    for token: Token in tokens.iter():
        tokenKinds.push(token.kind)

    if tokens.len() != expected.len():
        print("\t\tExpected `expected.len()` tokens, generated `tokens.len()` tokens.")
        print("\t\tExpected tokens:  `expected`")
        print("\t\tGenerated tokens: `tokenKinds`")

    for i: U32 in range(0u32, tokens.len()):
        if tokenKinds.get(i) != expected.get(i):
            print("\t\tToken `i` expected `expected.get(i)`, found `tokenKinds.get(i)`")
            return

    print("\t\tOK")

_scan(input: Str): [AssertionError(msg: Str), ..r] Vec[TokenKind]
    let (tokens, error) = tokenize("Test", input)
    if error is Option.Some(error):
        throw(~AssertionError(msg = "Lexer failed: `error.msg`"))
    let scanned = scan(tokens)
    let tokenKinds: Vec[TokenKind] = Vec.withCapacity(scanned.len())
    for token: Token in scanned.iter():
        tokenKinds.push(token.kind)
    tokenKinds
