# A self lexer.

type Token:
    kind: TokenKind
    text: Str
    byteIdx: U32

impl ToStr[Token]:
    toStr(self: Token): Str
        "`self.kind.toStr()`(`self.byteIdx.toStr()`, \"`self.text`\")"

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

impl ToStr[TokenKind]:
    toStr(self: TokenKind): Str
        match self:
            TokenKind.UpperId: "UpperId"
            TokenKind.LowerId: "LowerId"
            TokenKind.As: "As"
            TokenKind.Break: "Break"
            TokenKind.Continue: "Continue"
            TokenKind.Elif: "Elif"
            TokenKind.Else: "Else"
            TokenKind.Export: "Export"
            TokenKind.Fn_: "Fn"
            TokenKind.UpperFn: "UpperFn"
            TokenKind.For: "For"
            TokenKind.If: "If"
            TokenKind.Impl: "Impl"
            TokenKind.Import: "Import"
            TokenKind.In: "In"
            TokenKind.Jump: "Jump"
            TokenKind.Let: "Let"
            TokenKind.Match: "Match"
            TokenKind.Prim: "Prim"
            TokenKind.Return: "Return"
            TokenKind.Self_: "Self"
            TokenKind.Trait: "Trait"
            TokenKind.Type: "Type"
            TokenKind.Var: "Var"
            TokenKind.While: "While"
            TokenKind.LParen: "LParen"
            TokenKind.RParen: "RParen"
            TokenKind.LBracket: "LBracket"
            TokenKind.RBracket: "RBracket"
            TokenKind.LBrace: "LBrace"
            TokenKind.RBrace: "RBrace"
            TokenKind.SingleQuote: "SingleQuote"
            TokenKind.Colon: "Colon"
            TokenKind.Comma: "Comma"
            TokenKind.Dot: "Dot"
            TokenKind.Backslash: "Backslash"
            TokenKind.Underscore: "Underscore"
            TokenKind.Amp: "Amp"
            TokenKind.AmpAmp: "AmpAmp"
            TokenKind.DotDot: "DotDot"
            TokenKind.DotDotEq: "DotDotEq"
            TokenKind.Eq: "Eq"
            TokenKind.EqEq: "EqEq"
            TokenKind.Exclamation: "Exclamation"
            TokenKind.ExclamationEq: "ExclamationEq"
            TokenKind.LAngle: "LAngle"
            TokenKind.DoubleLAngle: "DoubleLAngle"
            TokenKind.LAngleEq: "LAngleEq"
            TokenKind.Minus: "Minus"
            TokenKind.MinusEq: "MinusEq"
            TokenKind.Pipe: "Pipe"
            TokenKind.PipePipe: "PipePipe"
            TokenKind.Plus: "Plus"
            TokenKind.PlusEq: "PlusEq"
            TokenKind.RAngle: "RAngle"
            TokenKind.DoubleRAngle: "DoubleRAngle"
            TokenKind.RAngleEq: "RAngleEq"
            TokenKind.Star: "Star"
            TokenKind.StarEq: "StarEq"
            TokenKind.String: "String"
            TokenKind.Int(kind): "Int(`kind.toStr()`)"
            TokenKind.HexInt(kind): "HexInt(`kind.toStr()`)"
            TokenKind.BinInt(kind): "BinInt(`kind.toStr()`)"
            TokenKind.Char(char): "Char(`char.toStr()`)"

type IntKind:
    I8
    U8
    I32
    U32

impl ToStr[IntKind]:
    toStr(self: IntKind): Str
        match self:
            IntKind.I8: "I8"
            IntKind.U8: "U8"
            IntKind.I32: "I32"
            IntKind.U32: "U32"

type Lexer:
    _input: Str
    _byteIdx: U32

# NB. Panics if OOB.
Lexer._nextChar(self): Char
    self._input.charAt(self._byteIdx)

Lexer.next(self): {LexerError(error: Str), ..r} Option[Token]
    if self._byteIdx == self._input.len():
        return Option.None

    while self._nextChar().isAsciiWhitespace():
        self._byteIdx += 1

    if self._nextChar() == '#':
        self._byteIdx += 1

        if self._byteIdx < self._input.len() && self._nextChar() == '|':
            self._byteIdx += 1
            self._skipMultiLineComment()
        else:
            self._skipSingleLineComment()

        return self.next()  # TODO: Make this `jump` once we have tail calls

    let byteIdx = self._byteIdx
    match self._input.substr(self._byteIdx, self._input.len()):
        ########################################################################################
        # Keywords

        "as" rest:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.As, text = "as", byteIdx = byteIdx))

        "break" rest:
            self._byteIdx += 5
            return Option.Some(Token(kind = TokenKind.Break, text = "break", byteIdx = byteIdx))

        "continue" rest:
            self._byteIdx += 8
            return Option.Some(Token(kind = TokenKind.Continue, text = "continue", byteIdx = byteIdx))

        "elif" rest:
            self._byteIdx += 4
            return Option.Some(Token(kind = TokenKind.Elif, text = "elif", byteIdx = byteIdx))

        "else" rest:
            self._byteIdx += 4
            return Option.Some(Token(kind = TokenKind.Else, text = "else", byteIdx = byteIdx))

        "export" rest:
            self._byteIdx += 6
            return Option.Some(Token(kind = TokenKind.Export, text = "export", byteIdx = byteIdx))

        "fn" rest:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.Fn_, text = "fn", byteIdx = byteIdx))

        "Fn" rest:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.UpperFn, text = "Fn", byteIdx = byteIdx))

        "for" rest:
            self._byteIdx += 3
            return Option.Some(Token(kind = TokenKind.For, text = "for", byteIdx = byteIdx))

        "if" rest:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.If, text = "if", byteIdx = byteIdx))

        "impl" rest:
            self._byteIdx += 4
            return Option.Some(Token(kind = TokenKind.Impl, text = "impl", byteIdx = byteIdx))

        "import" rest:
            self._byteIdx += 6
            return Option.Some(Token(kind = TokenKind.Import, text = "import", byteIdx = byteIdx))

        "in" rest:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.In, text = "in", byteIdx = byteIdx))

        "jump" rest:
            self._byteIdx += 4
            return Option.Some(Token(kind = TokenKind.Jump, text = "jump", byteIdx = byteIdx))

        "let" rest:
            self._byteIdx += 3
            return Option.Some(Token(kind = TokenKind.Let, text = "let", byteIdx = byteIdx))

        "match" rest:
            self._byteIdx += 5
            return Option.Some(Token(kind = TokenKind.Match, text = "match", byteIdx = byteIdx))

        "prim" rest:
            self._byteIdx += 4
            return Option.Some(Token(kind = TokenKind.Prim, text = "prim", byteIdx = byteIdx))

        "return" rest:
            self._byteIdx += 6
            return Option.Some(Token(kind = TokenKind.Return, text = "return", byteIdx = byteIdx))

        "self" rest:
            self._byteIdx += 4
            return Option.Some(Token(kind = TokenKind.Self_, text = "self", byteIdx = byteIdx))

        "trait" rest:
            self._byteIdx += 5
            return Option.Some(Token(kind = TokenKind.Trait, text = "trait", byteIdx = byteIdx))

        "type" rest:
            self._byteIdx += 4
            return Option.Some(Token(kind = TokenKind.Type, text = "type", byteIdx = byteIdx))

        "var" rest:
            self._byteIdx += 3
            return Option.Some(Token(kind = TokenKind.Var, text = "var", byteIdx = byteIdx))

        "while" rest:
            self._byteIdx += 5
            return Option.Some(Token(kind = TokenKind.While, text = "while", byteIdx = byteIdx))

        ########################################################################################
        # Delimiters

        "(" rest:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.LParen, text = "(", byteIdx = byteIdx))

        ")" rest:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.RParen, text = ")", byteIdx = byteIdx))

        "[" rest:
            return Option.Some(Token(kind = TokenKind.LBracket, text = "[", byteIdx = byteIdx))
            self._byteIdx += 1

        "]" rest:
            return Option.Some(Token(kind = TokenKind.RBracket, text = "]", byteIdx = byteIdx))
            self._byteIdx += 1

        "{" rest:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.LBrace, text = "{", byteIdx = byteIdx))

        "}" rest:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.RBrace, text = "}", byteIdx = byteIdx))

        ########################################################################################
        # Punctuation

        "." rest:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.Dot, text = ".", byteIdx = byteIdx))

        "," rest:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.Comma, text = ",", byteIdx = byteIdx))

        ":" rest:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.Colon, text = ":", byteIdx = byteIdx))

        "..=" rest:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.DotDotEq, text = "..=", byteIdx = byteIdx))

        ".." rest:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.DotDot, text = "..", byteIdx = byteIdx))

        ########################################################################################
        # Operators

        "==" rest:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.EqEq, text = "==", byteIdx = byteIdx))

        "=" rest:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.Eq, text = "=", byteIdx = byteIdx))

        "+=" rest:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.PlusEq, text = "+=", byteIdx = byteIdx))

        "-=" rest:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.MinusEq, text = "-=", byteIdx = byteIdx))

        "*=" rest:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.StarEq, text = "*=", byteIdx = byteIdx))

        "+" rest:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.Plus, text = "+", byteIdx = byteIdx))

        # TODO: Handle negative numbers here by checking whether `rest` starts with a digit.
        "-" rest:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.Minus, text = "-", byteIdx = byteIdx))

        "*" rest:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.Star, text = "*", byteIdx = byteIdx))

        "!=" rest:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.ExclamationEq, text = "!=", byteIdx = byteIdx))

        "!" rest:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.Exclamation, text = "!", byteIdx = byteIdx))

        "&&" rest:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.AmpAmp, text = "&&", byteIdx = byteIdx))

        "&" rest:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.Amp, text = "&", byteIdx = byteIdx))

        "||" rest:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.PipePipe, text = "||", byteIdx = byteIdx))

        "|" rest:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.PipePipe, text = "|", byteIdx = byteIdx))

        "<<" rest:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.DoubleLAngle, text = "<<", byteIdx = byteIdx))

        "<=" rest:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.LAngleEq, text = "<=", byteIdx = byteIdx))

        "<" rest:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.LAngle, text = "<", byteIdx = byteIdx))

        ">>" rest:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.DoubleRAngle, text = ">>", byteIdx = byteIdx))

        ">=" rest:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.RAngleEq, text = ">=", byteIdx = byteIdx))

        ">" rest:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.RAngle, text = ">", byteIdx = byteIdx))

        ########################################################################################
        # Literals

        "\"" rest:
            return Option.Some(self._string())

        "'" rest:
            return Option.Some(self._char())

        "0b" rest:
            panic("TODO")

        "0x" rest:
            panic("TODO")

        other:
            let c = self._nextChar()

            if c.isAsciiDigit():
                let digitsStart = self._byteIdx
                self._byteIdx += 1

                let digitsEnd = self._byteIdx
                while digitsEnd < self._input.len():
                    let c = self._input.charAt(digitsEnd)
                    if c != '_' && !c.isAsciiDigit():
                        break
                    digitsEnd += 1

                self._byteIdx = digitsEnd

                # Check type suffix
                let rest = self._input.substr(digitsEnd, self._input.len())
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

                return Option.Some(Token(
                    kind = TokenKind.Int(Option.Some(typeSuffix)),
                    text = self._input.substr(digitsStart, digitsEnd),
                    byteIdx = byteIdx,
                ))

            let uppercaseId = c.isAsciiUppercase()

            # TODO: This is a bug in the Rust lexer as well: we should _a
            # should be lowercase, _A should be uppercase.
            let lowercaseId = c.isAsciiLowercase() || c == '_'

            if uppercaseId || lowercaseId:
                let endIdx = self._byteIdx + 1
                while self._input.len() > endIdx && isIdCont(self._input.charAt(endIdx)):
                    endIdx += 1
                let id = self._input.substr(self._byteIdx, endIdx)
                let kind = if uppercaseId:
                    TokenKind.UpperId
                else:
                    TokenKind.LowerId
                self._byteIdx = endIdx
                return Option.Some(Token(
                    kind = kind,
                    text = id,
                    byteIdx = byteIdx
                ))

            panic("TODO: `c.toStr()` at `byteIdx.toStr()`")

    throw(~LexerError(error = "unterminated string"))

# NB. Initial '"' should NOT be consumed.
Lexer._string(self): {LexerError(error: Str), ..errs} Token
    let startIdx = self._byteIdx
    self._byteIdx += 1 # Skip initial '#'
    while self._byteIdx < self._input.len():
        match self._nextChar():
            '"':
                self._byteIdx += 1
                return Token(
                    kind = TokenKind.String,
                    text = self._input.substr(startIdx, self._byteIdx),
                    byteIdx = startIdx
                )

            '`':
                # TODO: Allow nesting.
                # Nesting needs to be handled in coordination with the parser,
                # as the lexer cannot (or should not) keep track of the brackets
                # and maintain a tree structure.
                # This means we won't be able to tokenize files without the help.
                self._byteIdx += 1
                while self._byteIdx < self._input.len():
                    match self._nextChar():
                        '`':
                            self._byteIdx += 1
                            break

                        _:
                            self._byteIdx += 1

            '\\':
                self._byteIdx += 1
                match self._nextChar():
                    '`' | '"' | 'n' | 't' | 'r' | '\\':
                        self._byteIdx += 1
                    other:
                        throw(~LexerError(error = "invalid escape: '`other.toStr()`'"))

            _: self._byteIdx += 1

    throw(~LexerError(error = "unterminated string literal"))

# NB. Initial '\'' should NOT be consumed.
Lexer._char(self): {LexerError(error: Str), ..errs} Token
    let idx = self._byteIdx
    self._byteIdx += 1
    let char = match self._nextChar():
        '\\':
            self._byteIdx += 1
            match self._nextChar():
                '\'': '\''
                '\\': '\\'
                'n': '\n'
                't': '\t'
                'r': '\r'
                other: throw(~LexerError(error = "invalid escape character in character literal: '`other.toStr()`'"))
        c: c
    self._byteIdx += 1
    if self._nextChar() != '\'':
        throw(~LexerError(error = "unterminated character literal"))

    self._byteIdx += 1
    Token(kind = TokenKind.Char(char), text = self._input.substr(idx, self._byteIdx), byteIdx = idx)

Lexer._skipSingleLineComment(self)
    while self._byteIdx < self._input.len():
        let c = self._nextChar()
        self._byteIdx += 1
        if c == '\n':
            return ()

Lexer._skipMultiLineComment(self): {LexerError(error: Str), ..r}
    while self._byteIdx < self._input.len():
        let c = self._nextChar()
        self._byteIdx += 1
        if c == '|':
            if self._byteIdx < self._input.len():
                let c = self._nextChar()
                if c == '#':
                    self._byteIdx += 1
                    return ()

    throw(~LexerError(error = "unterminated multi-line comment"))

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
    for token: Token in tokens.iter():
        printStr(token.toStr())
    ()
