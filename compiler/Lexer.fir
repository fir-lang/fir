import Ast
import Error
import Token

type Lexer:
    _file: Str
    _input: Str
    _byteIdx: U32

Lexer._fail(self, msg: Str): Error a
    throw(Error(loc = Loc(file = self._file, byteIdx = self._byteIdx, byteLen = 0), msg = msg))

# NB. Panics if OOB.
Lexer._nextChar(self): Char
    self._input.charAt(self._byteIdx)

Lexer.next(self): Error Option[Token]
    while self._byteIdx < self._input.len() && self._nextChar().isAsciiWhitespace():
        self._byteIdx += 1

    if self._byteIdx == self._input.len():
        return Option.None

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

        "as" _:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.As, text = "as", byteIdx = byteIdx))

        "break" _:
            self._byteIdx += 5
            return Option.Some(Token(kind = TokenKind.Break, text = "break", byteIdx = byteIdx))

        "continue" _:
            self._byteIdx += 8
            return Option.Some(Token(kind = TokenKind.Continue, text = "continue", byteIdx = byteIdx))

        "elif" _:
            self._byteIdx += 4
            return Option.Some(Token(kind = TokenKind.Elif, text = "elif", byteIdx = byteIdx))

        "else" _:
            self._byteIdx += 4
            return Option.Some(Token(kind = TokenKind.Else, text = "else", byteIdx = byteIdx))

        "export" _:
            self._byteIdx += 6
            return Option.Some(Token(kind = TokenKind.Export, text = "export", byteIdx = byteIdx))

        "fn" _:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.Fn_, text = "fn", byteIdx = byteIdx))

        "Fn" _:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.UpperFn, text = "Fn", byteIdx = byteIdx))

        "for" _:
            self._byteIdx += 3
            return Option.Some(Token(kind = TokenKind.For, text = "for", byteIdx = byteIdx))

        "if" _:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.If, text = "if", byteIdx = byteIdx))

        "impl" _:
            self._byteIdx += 4
            return Option.Some(Token(kind = TokenKind.Impl, text = "impl", byteIdx = byteIdx))

        "import" _:
            self._byteIdx += 6
            return Option.Some(Token(kind = TokenKind.Import, text = "import", byteIdx = byteIdx))

        "in" _:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.In, text = "in", byteIdx = byteIdx))

        "jump" _:
            self._byteIdx += 4
            return Option.Some(Token(kind = TokenKind.Jump, text = "jump", byteIdx = byteIdx))

        "let" _:
            self._byteIdx += 3
            return Option.Some(Token(kind = TokenKind.Let, text = "let", byteIdx = byteIdx))

        "match" _:
            self._byteIdx += 5
            return Option.Some(Token(kind = TokenKind.Match, text = "match", byteIdx = byteIdx))

        "prim" _:
            self._byteIdx += 4
            return Option.Some(Token(kind = TokenKind.Prim, text = "prim", byteIdx = byteIdx))

        "return" _:
            self._byteIdx += 6
            return Option.Some(Token(kind = TokenKind.Return, text = "return", byteIdx = byteIdx))

        "self" _:
            self._byteIdx += 4
            return Option.Some(Token(kind = TokenKind.Self_, text = "self", byteIdx = byteIdx))

        "trait" _:
            self._byteIdx += 5
            return Option.Some(Token(kind = TokenKind.Trait, text = "trait", byteIdx = byteIdx))

        "type" _:
            self._byteIdx += 4
            return Option.Some(Token(kind = TokenKind.Type, text = "type", byteIdx = byteIdx))

        "var" _:
            self._byteIdx += 3
            return Option.Some(Token(kind = TokenKind.Var, text = "var", byteIdx = byteIdx))

        "while" _:
            self._byteIdx += 5
            return Option.Some(Token(kind = TokenKind.While, text = "while", byteIdx = byteIdx))

        ########################################################################################
        # Delimiters

        "(" _:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.LParen, text = "(", byteIdx = byteIdx))

        ")" _:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.RParen, text = ")", byteIdx = byteIdx))

        "[" _:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.LBracket, text = "[", byteIdx = byteIdx))

        "]" _:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.RBracket, text = "]", byteIdx = byteIdx))

        "{" _:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.LBrace, text = "{", byteIdx = byteIdx))

        "}" _:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.RBrace, text = "}", byteIdx = byteIdx))

        ########################################################################################
        # Punctuation

        "." _:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.Dot, text = ".", byteIdx = byteIdx))

        "," _:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.Comma, text = ",", byteIdx = byteIdx))

        ":" _:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.Colon, text = ":", byteIdx = byteIdx))

        "..=" _:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.DotDotEq, text = "..=", byteIdx = byteIdx))

        ".." _:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.DotDot, text = "..", byteIdx = byteIdx))

        ########################################################################################
        # Operators

        "==" _:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.EqEq, text = "==", byteIdx = byteIdx))

        "=" _:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.Eq, text = "=", byteIdx = byteIdx))

        "+=" _:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.PlusEq, text = "+=", byteIdx = byteIdx))

        "-=" _:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.MinusEq, text = "-=", byteIdx = byteIdx))

        "*=" _:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.StarEq, text = "*=", byteIdx = byteIdx))

        "+" _:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.Plus, text = "+", byteIdx = byteIdx))

        # TODO: Handle negative numbers here by checking whether `rest` starts with a digit.
        "-" rest:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.Minus, text = "-", byteIdx = byteIdx))

        "*" _:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.Star, text = "*", byteIdx = byteIdx))

        "!=" _:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.ExclamationEq, text = "!=", byteIdx = byteIdx))

        "!" _:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.Exclamation, text = "!", byteIdx = byteIdx))

        "&&" _:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.AmpAmp, text = "&&", byteIdx = byteIdx))

        "&" _:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.Amp, text = "&", byteIdx = byteIdx))

        "||" _:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.PipePipe, text = "||", byteIdx = byteIdx))

        "|" _:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.PipePipe, text = "|", byteIdx = byteIdx))

        "<<" _:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.DoubleLAngle, text = "<<", byteIdx = byteIdx))

        "<=" _:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.LAngleEq, text = "<=", byteIdx = byteIdx))

        "<" _:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.LAngle, text = "<", byteIdx = byteIdx))

        ">>" _:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.DoubleRAngle, text = ">>", byteIdx = byteIdx))

        ">=" _:
            self._byteIdx += 2
            return Option.Some(Token(kind = TokenKind.RAngleEq, text = ">=", byteIdx = byteIdx))

        ">" _:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.RAngle, text = ">", byteIdx = byteIdx))

        "/" _:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.Slash, text = "/", byteIdx = byteIdx))

        "\\" _:
            self._byteIdx += 1
            return Option.Some(Token(kind = TokenKind.Backslash, text = "\\", byteIdx = byteIdx))

        ########################################################################################
        # Literals

        "\"" _:
            return Option.Some(self._string())

        "'" _:
            return Option.Some(self._char())

        "0b" _:
            let digitsStart = self._byteIdx
            self._byteIdx += 1

            while self._byteIdx < self._input.len():
                let c = self._nextChar()
                if c != '_' && !c.isAsciiBinDigit():
                    break
                self._byteIdx += 1

            let typeSuffix = self._intTypeSuffix()
            return Option.Some(Token(
                kind = TokenKind.Int(Option.Some(typeSuffix)),
                text = self._input.substr(digitsStart, self._byteIdx),
                byteIdx = byteIdx,
            ))

        "0x" _:
            let digitsStart = self._byteIdx
            self._byteIdx += 1

            while self._byteIdx < self._input.len():
                let c = self._nextChar()
                if c != '_' || !c.isAsciiHexDigit():
                    break
                self._byteIdx += 1

            let typeSuffix = self._intTypeSuffix()
            return Option.Some(Token(
                kind = TokenKind.Int(Option.Some(typeSuffix)),
                text = self._input.substr(digitsStart, self._byteIdx),
                byteIdx = byteIdx,
            ))

        "~" _:
            let idStart = self._byteIdx
            self._byteIdx += 1
            if self._byteIdx < self._input.len() && self._nextChar().isAsciiUppercase():
                self._byteIdx += 1
                while self._byteIdx < self._input.len() && _isIdCont(self._nextChar()):
                    self._byteIdx += 1
                return Option.Some(Token(
                    kind = TokenKind.TildeUpperId,
                    text = self._input.substr(idStart, self._byteIdx),
                    byteIdx = idStart,
                ))
            else:
                return Option.Some(Token(
                    kind = TokenKind.Tilde,
                    text = "~",
                    byteIdx = idStart,
                ))

        other:
            let c = self._nextChar()

            if c.isAsciiDigit():
                let digitsStart = self._byteIdx
                self._byteIdx += 1

                while self._byteIdx < self._input.len():
                    let c = self._nextChar()
                    if c != '_' && !c.isAsciiDigit():
                        break
                    self._byteIdx += 1

                let typeSuffix = self._intTypeSuffix()
                return Option.Some(Token(
                    kind = TokenKind.Int(Option.Some(typeSuffix)),
                    text = self._input.substr(digitsStart, self._byteIdx),
                    byteIdx = byteIdx,
                ))

            let uppercaseId = c.isAsciiUppercase()

            # TODO: This is a bug in the Rust lexer as well: _a should be
            # lowercase, _A should be uppercase.
            let lowercaseId = c.isAsciiLowercase() || c == '_'

            if uppercaseId || lowercaseId:
                let endIdx = self._byteIdx + 1
                while self._input.len() > endIdx && _isIdCont(self._input.charAt(endIdx)):
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

            panic("TODO: `c` at `byteIdx`")

Lexer._intTypeSuffix(self): Error IntKind
    let rest = self._input.substr(self._byteIdx, self._input.len())
    let typeSuffix = IntKind.U32
    match rest:
        "u8" _:
            typeSuffix = IntKind.U8
            self._byteIdx += 2
        "i8" _:
            typeSuffix = IntKind.I8
            self._byteIdx += 2
        "u32" _:
            typeSuffix = IntKind.U32
            self._byteIdx += 3
        "i32" _:
            typeSuffix = IntKind.I32
            self._byteIdx += 3
        _:
            ()
    typeSuffix

# NB. Initial '"' should NOT be consumed.
Lexer._string(self): Error Token
    let startIdx = self._byteIdx
    self._byteIdx += 1 # Skip initial '#'
    while self._byteIdx < self._input.len():
        match self._nextChar():
            '"':
                self._byteIdx += 1
                return Token(
                    kind = TokenKind.Str,
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
                        self._fail("invalid escape: '`other`'")

            other: self._byteIdx += other.lenUtf8()

    self._fail("unterminated string literal")

# NB. Initial '\'' should NOT be consumed.
Lexer._char(self): Error Token
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
                other: self._fail("invalid escape character in character literal: '`other`'")
        c: c
    self._byteIdx += char.lenUtf8()
    if self._nextChar() != '\'':
        self._fail("unterminated character literal")

    self._byteIdx += 1
    Token(kind = TokenKind.Char, text = self._input.substr(idx, self._byteIdx), byteIdx = idx)

Lexer._skipSingleLineComment(self)
    while self._byteIdx < self._input.len():
        let c = self._nextChar()
        self._byteIdx += c.lenUtf8()
        if c == '\n':
            return

Lexer._skipMultiLineComment(self): Error ()
    while self._byteIdx < self._input.len():
        let c = self._nextChar()
        self._byteIdx += c.lenUtf8()
        if c == '|':
            if self._byteIdx < self._input.len():
                let c = self._nextChar()
                if c == '#':
                    self._byteIdx += 1
                    return

    self._fail("unterminated multi-line comment")

_isIdCont(c: Char): Bool
    c.isAsciiAlphanumeric() || c == '_'

tokenize(file: Str, contents: Str): (tokens: Vec[Token], error: Option[Error])
    let tokens = Vec.withCapacity(1000)
    let lexer = Lexer(_file = file, _input = contents, _byteIdx = 0)
    loop:
        match try(lexer.next):
            Result.Ok(Option.None): break
            Result.Ok(Option.Some(t)): tokens.push(t)
            Result.Err(error): return (tokens = tokens, error = Option.Some(error))
    (tokens = tokens, error = Option.None)
