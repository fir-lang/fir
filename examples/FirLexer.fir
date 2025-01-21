# A self lexer.

type Token:
    kind: TokenKind
    text: Str
    byteIdx: U32

type TokenKind:
    # An identifier starting with an uppercase letter.
    UpperId

    # An identifier starting with a lowercase letter.
    LowerId

    # Keywords
    As
    Break
    Continue
    Elif
    Else
    Export
    Fn_
    UpperFn
    For
    If
    Impl
    Import
    In
    Jump
    Let
    Match
    Prim
    Return
    Self_
    Trait
    Type
    Var
    While

    # Delimiters
    LParen
    RParen
    LBracket
    RBracket
    LBrace
    RBrace
    SingleQuote

    # Punctuation
    Colon
    Comma
    Dot
    Backslash
    Underscore

    # Operators
    Amp
    AmpAmp
    DotDot
    DotDotEq
    Eq
    EqEq
    Exclamation
    ExclamationEq
    LAngle
    DoubleLAngle
    LAngleEq
    Minus
    MinusEq
    Pipe
    PipePipe
    Plus
    PlusEq
    RAngle
    DoubleRAngle
    RAngleEq
    Star
    StarEq

    # Literals
    String
    Int(Option[IntKind])
    HexInt(Option[IntKind])
    BinInt(Option[IntKind])
    Char(Char)

type IntKind:
    I8
    U8
    I32
    U32

tokenize(input: Str): Vec[Token]
    let tokens = Vec.withCapacity(1000)
    tokenize_(input, 0, tokens)
    tokens

tokenize_(input: Str, byteIdx: U32, tokens: Vec[Token])
    while byteIdx < input.len():
        let c = input.charAt(byteIdx)
        if c.isAsciiWhitespace():
            byteIdx += 1
            continue

        if c == '#':
            byteIdx += 1
            if byteIdx < input.len() && input.charAt(byteIdx) == '|':
                byteIdx += 1
                byteIdx = skipMultiLineComment(input, byteIdx)
            else:
                byteIdx = skipSingleLineComment(input, byteIdx)
            continue

        match input.substr(byteIdx, input.len()):
            ########################################################################################
            # Keywords

            "as" rest:
                tokens.push(Token(kind = TokenKind.As, text = "as", byteIdx = byteIdx))
                byteIdx += 2

            "break" rest:
                tokens.push(Token(kind = TokenKind.Break, text = "break", byteIdx = byteIdx))
                byteIdx += 5

            "continue" rest:
                tokens.push(Token(kind = TokenKind.Continue, text = "continue", byteIdx = byteIdx))
                byteIdx += 8

            "elif" rest:
                tokens.push(Token(kind = TokenKind.Elif, text = "elif", byteIdx = byteIdx))
                byteIdx += 4

            "else" rest:
                tokens.push(Token(kind = TokenKind.Else, text = "else", byteIdx = byteIdx))
                byteIdx += 4

            "export" rest:
                tokens.push(Token(kind = TokenKind.Export, text = "export", byteIdx = byteIdx))
                byteIdx += 6

            "fn" rest:
                tokens.push(Token(kind = TokenKind.Fn_, text = "fn", byteIdx = byteIdx))
                byteIdx += 2

            "Fn" rest:
                tokens.push(Token(kind = TokenKind.UpperFn, text = "Fn", byteIdx = byteIdx))
                byteIdx += 2

            "for" rest:
                tokens.push(Token(kind = TokenKind.For, text = "for", byteIdx = byteIdx))
                byteIdx += 3

            "if" rest:
                tokens.push(Token(kind = TokenKind.If, text = "if", byteIdx = byteIdx))
                byteIdx += 2

            "impl" rest:
                tokens.push(Token(kind = TokenKind.Impl, text = "impl", byteIdx = byteIdx))
                byteIdx += 4

            "import" rest:
                tokens.push(Token(kind = TokenKind.Import, text = "import", byteIdx = byteIdx))
                byteIdx += 6

            "in" rest:
                tokens.push(Token(kind = TokenKind.In, text = "in", byteIdx = byteIdx))
                byteIdx += 2

            "jump" rest:
                tokens.push(Token(kind = TokenKind.Jump, text = "jump", byteIdx = byteIdx))
                byteIdx += 4

            "let" rest:
                tokens.push(Token(kind = TokenKind.Let, text = "let", byteIdx = byteIdx))
                byteIdx += 3

            "match" rest:
                tokens.push(Token(kind = TokenKind.Match, text = "match", byteIdx = byteIdx))
                byteIdx += 5

            "prim" rest:
                tokens.push(Token(kind = TokenKind.Prim, text = "prim", byteIdx = byteIdx))
                byteIdx += 4

            "return" rest:
                tokens.push(Token(kind = TokenKind.Return, text = "return", byteIdx = byteIdx))
                byteIdx += 6

            "self" rest:
                tokens.push(Token(kind = TokenKind.Self_, text = "self", byteIdx = byteIdx))
                byteIdx += 4

            "trait" rest:
                tokens.push(Token(kind = TokenKind.Trait, text = "trait", byteIdx = byteIdx))
                byteIdx += 5

            "type" rest:
                tokens.push(Token(kind = TokenKind.Type, text = "type", byteIdx = byteIdx))
                byteIdx += 4

            "var" rest:
                tokens.push(Token(kind = TokenKind.Var, text = "var", byteIdx = byteIdx))
                byteIdx += 3

            "while" rest:
                tokens.push(Token(kind = TokenKind.While, text = "while", byteIdx = byteIdx))
                byteIdx += 5

            ########################################################################################
            # Delimiters

            "(" rest:
                tokens.push(Token(kind = TokenKind.LParen, text = "(", byteIdx = byteIdx))
                byteIdx += 1

            ")" rest:
                tokens.push(Token(kind = TokenKind.RParen, text = ")", byteIdx = byteIdx))
                byteIdx += 1

            "[" rest:
                tokens.push(Token(kind = TokenKind.LBracket, text = "[", byteIdx = byteIdx))
                byteIdx += 1

            "]" rest:
                tokens.push(Token(kind = TokenKind.RBracket, text = "]", byteIdx = byteIdx))
                byteIdx += 1

            "{" rest:
                tokens.push(Token(kind = TokenKind.LBrace, text = "{", byteIdx = byteIdx))
                byteIdx += 1

            "}" rest:
                tokens.push(Token(kind = TokenKind.RBrace, text = "}", byteIdx = byteIdx))
                byteIdx += 1

            ########################################################################################
            # Punctuation

            "." rest:
                tokens.push(Token(kind = TokenKind.Dot, text = ".", byteIdx = byteIdx))
                byteIdx += 1

            "," rest:
                tokens.push(Token(kind = TokenKind.Comma, text = ",", byteIdx = byteIdx))
                byteIdx += 1

            ":" rest:
                tokens.push(Token(kind = TokenKind.Colon, text = ":", byteIdx = byteIdx))
                byteIdx += 1

            # "\\" rest:
            #     tokens.push(Token(kind = TokenKind.Backslash, text = "\\", byteIdx = byteIdx))
            #     byteIdx += 1

            "..=" rest:
                tokens.push(Token(kind = TokenKind.DotDotEq, text = "..=", byteIdx = byteIdx))
                byteIdx += 1

            ".." rest:
                tokens.push(Token(kind = TokenKind.DotDot, text = "..", byteIdx = byteIdx))
                byteIdx += 1

            ########################################################################################
            # Operators

            "==" rest:
                tokens.push(Token(kind = TokenKind.EqEq, text = "==", byteIdx = byteIdx))
                byteIdx += 2

            "=" rest:
                tokens.push(Token(kind = TokenKind.Eq, text = "=", byteIdx = byteIdx))
                byteIdx += 1

            "+=" rest:
                tokens.push(Token(kind = TokenKind.PlusEq, text = "+=", byteIdx = byteIdx))
                byteIdx += 2

            "-=" rest:
                tokens.push(Token(kind = TokenKind.MinusEq, text = "-=", byteIdx = byteIdx))
                byteIdx += 2

            "*=" rest:
                tokens.push(Token(kind = TokenKind.StarEq, text = "*=", byteIdx = byteIdx))
                byteIdx += 2

            "+" rest:
                tokens.push(Token(kind = TokenKind.Plus, text = "+", byteIdx = byteIdx))
                byteIdx += 1

            # TODO: Handle negative numbers here by checking whether `rest` starts with a digit.
            "-" rest:
                tokens.push(Token(kind = TokenKind.Minus, text = "-", byteIdx = byteIdx))
                byteIdx += 1

            "*" rest:
                tokens.push(Token(kind = TokenKind.Star, text = "*", byteIdx = byteIdx))
                byteIdx += 1

            "!=" rest:
                tokens.push(Token(kind = TokenKind.ExclamationEq, text = "!=", byteIdx = byteIdx))
                byteIdx += 2

            "!" rest:
                tokens.push(Token(kind = TokenKind.Exclamation, text = "!", byteIdx = byteIdx))
                byteIdx += 1

            "&&" rest:
                tokens.push(Token(kind = TokenKind.AmpAmp, text = "&&", byteIdx = byteIdx))
                byteIdx += 2

            "&" rest:
                tokens.push(Token(kind = TokenKind.Amp, text = "&", byteIdx = byteIdx))
                byteIdx += 1

            "||" rest:
                tokens.push(Token(kind = TokenKind.PipePipe, text = "||", byteIdx = byteIdx))
                byteIdx += 2

            "|" rest:
                tokens.push(Token(kind = TokenKind.PipePipe, text = "|", byteIdx = byteIdx))
                byteIdx += 1

            "<<" rest:
                tokens.push(Token(kind = TokenKind.DoubleLAngle, text = "<<", byteIdx = byteIdx))
                byteIdx += 2

            "<=" rest:
                tokens.push(Token(kind = TokenKind.LAngleEq, text = "<=", byteIdx = byteIdx))
                byteIdx += 2

            "<" rest:
                tokens.push(Token(kind = TokenKind.LAngle, text = "<", byteIdx = byteIdx))
                byteIdx += 1

            ">>" rest:
                tokens.push(Token(kind = TokenKind.DoubleRAngle, text = ">>", byteIdx = byteIdx))
                byteIdx += 2

            ">=" rest:
                tokens.push(Token(kind = TokenKind.RAngleEq, text = ">=", byteIdx = byteIdx))
                byteIdx += 2

            ">" rest:
                tokens.push(Token(kind = TokenKind.RAngle, text = ">", byteIdx = byteIdx))
                byteIdx += 1

            ########################################################################################
            # Literals

            "\"" rest:
                let startIdx = byteIdx
                byteIdx += 1
                while byteIdx < input.len():
                    match input.charAt(byteIdx):
                        '"':
                            byteIdx += 1
                            break

                        '`':
                            byteIdx += 1
                            while byteIdx < input.len():
                                match input.charAt(byteIdx):
                                    '`':
                                        byteIdx += 1
                                        break

                                    _:
                                        byteIdx += 1

                        '\\':
                            byteIdx += 1
                            match input.charAt(byteIdx):
                                '`' | '"' | 'n' | 't' | 'r' | '\\':
                                    byteIdx += 1
                                _:
                                    panic("Invalid escape")

                        _: byteIdx += 1

                tokens.push(Token(kind = TokenKind.String, text = input.substr(startIdx, byteIdx), byteIdx = startIdx))

            "'" rest:
                let idx = byteIdx + 1
                let char = match input.charAt(idx):
                    '\\':
                        idx += 1
                        match input.charAt(idx):
                            '\'': '\''
                            '\\': '\\'
                            'n': '\n'
                            't': '\t'
                            'r': '\r'
                            other: panic("Invalid escape character in character literal at `idx.toStr()`")
                    c: c
                idx += 1
                if input.charAt(idx) != '\'':
                    panic("Unterminated character literal at `idx.toStr()`")

                tokens.push(Token(kind = TokenKind.Char(c), text = input.substr(byteIdx, idx + 1), byteIdx = byteIdx))
                byteIdx = idx + 1

            "0b" rest:
                panic("TODO")

            "0x" rest:
                panic("TODO")

            other:
                if c.isAsciiDigit():
                    let digitsStart = byteIdx
                    byteIdx += 1

                    let digitsEnd = byteIdx
                    while digitsEnd < input.len():
                        let c = input.charAt(digitsEnd)
                        if c != '_' && !c.isAsciiDigit():
                            break
                        digitsEnd += 1

                    byteIdx = digitsEnd

                    # Check type suffix
                    let rest = input.substr(digitsEnd, input.len())
                    let typeSuffix = IntKind.U32
                    match rest:
                        "u8" rest:
                            typeSuffix = IntKind.U8
                            byteIdx += 2
                        "i8" rest:
                            typeSuffix = IntKind.I8
                            byteIdx += 2
                        "u32" rest:
                            typeSuffix = IntKind.U32
                            byteIdx += 3
                        "i32" rest:
                            typeSuffix = IntKind.I32
                            byteIdx += 3
                        _:
                            ()

                    tokens.push(Token(
                        kind = TokenKind.Int(Option.Some(typeSuffix)),
                        text = input.substr(digitsStart, digitsEnd),
                        byteIdx = byteIdx,
                    ))

                    continue

                let uppercaseId = c.isAsciiUppercase()

                # TODO: This is a bug in the Rust lexer as well: we should _a
                # should be lowercase, _A should be uppercase.
                let lowercaseId = c.isAsciiLowercase() || c == '_'

                if uppercaseId || lowercaseId:
                    let endIdx = byteIdx + 1
                    while input.len() > endIdx && isIdCont(input.charAt(endIdx)):
                        endIdx += 1
                    let id = input.substr(byteIdx, endIdx)
                    let kind = if uppercaseId:
                        TokenKind.UpperId
                    else:
                        TokenKind.LowerId
                    tokens.push(Token(
                        kind = kind,
                        text = id,
                        byteIdx = byteIdx
                    ))
                    byteIdx = endIdx
                    continue

                panic("TODO: `c.toStr()` at `byteIdx.toStr()`")

isIdCont(c: Char): Bool
    c.isAsciiAlphanumeric() || c == '_'

# TODO: Handle nested comments.
skipMultiLineComment(input: Str, byteIdx: U32): U32
    while byteIdx < input.len():
        let c = input.charAt(byteIdx)
        byteIdx += 1
        if c == '|':
            if byteIdx < input.len():
                let c = input.charAt(byteIdx)
                if c == '#':
                    return byteIdx + 1

    panic("Unterminated multi-line comment")

skipSingleLineComment(input: Str, byteIdx: U32): U32
    while byteIdx < input.len():
        let c = input.charAt(byteIdx)
        byteIdx += 1
        if c == '\n':
            break

    byteIdx

main(args: Array[Str])
    let filePath = args.get(1)
    let fileContents = readFileUtf8(filePath)
    let tokens = tokenize(fileContents)
    ()
