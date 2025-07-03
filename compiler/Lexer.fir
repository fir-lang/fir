import Error
import Token


tokenize(file: Str, contents: Str) (tokens: Vec[Token], error: Option[Error]):
    let tokens = Vec.withCapacity(1000)
    let lexer = Lexer(_file = file, _input = contents, _byteIdx = 0, _line = 0, _col = 0)
    loop:
        match try(lexer._next):
            Result.Ok(Option.None): break
            Result.Ok(Option.Some(t)): tokens.push(t)
            Result.Err(error): return (tokens = tokens, error = Option.Some(error))
    let tokens = _combineTokens(contents, tokens)
    (tokens = tokens, error = Option.None)


# This is mainly for compatibility with the interpreter, to make it easier to test the compiler.
#
# In the interpreter we combine some of the tokens to make it easier to parse as LR(1).
#
# In the compiler we don't use LR(1), and PEG can do arbitrary lookahead (by trying to parse the
# lookahead and backtracking when failing), so technically we shouldn't need this. We may want to
# remove this once the compiler works and we no longer need the interpreter.
_combineTokens(contents: Str, tokens: Vec[Token]) Vec[Token]:
    let newTokens = Vec.withCapacity(tokens.len())

    let i = u32(0)
    while i < tokens.len():
        let token = tokens.get(i)

        match token.kind:
            TokenKind.TildeUpperId:
                if i + 2 < tokens.len()
                        and tokens.get(i + 1).kind is TokenKind.Dot
                        and tokens.get(i + 2) is Token(kind = TokenKind.UpperId, byteIdx = byteIdxRight, text = textRight, ..):
                    newTokens.push(Token(
                        kind = TokenKind.TildeUpperIdPath,
                        text = contents.substr(token.byteIdx, byteIdxRight + textRight.len()),
                        byteIdx = token.byteIdx,
                        line = token.line,
                        col = token.col,
                    ))
                    i += 3
                    continue

            TokenKind.UpperId:
                if i + 2 < tokens.len():
                    if tokens.get(i + 1).kind is TokenKind.Dot:
                        let next = tokens.get(i + 2)
                        if next is Token(kind = TokenKind.UpperId, byteIdx = byteIdxRight, text = textRight, ..):
                            newTokens.push(Token(
                                kind = TokenKind.UpperIdPath,
                                text = contents.substr(token.byteIdx, byteIdxRight + textRight.len()),
                                byteIdx = token.byteIdx,
                                line = token.line,
                                col = token.col,
                            ))
                            i += 3
                            continue
                        elif next.kind is TokenKind.LBracket:
                            newTokens.push(Token(
                                kind = TokenKind.UpperIdDotLBracket,
                                text = contents.substr(token.byteIdx, token.byteIdx + 2),
                                byteIdx = token.byteIdx,
                                line = token.line,
                                col = token.col,
                            ))
                            i += 3
                            continue

            _: ()

        newTokens.push(token)
        i += 1

    newTokens

## Entry point to tokenize file in command line argument and print generated tokens.
##
## Used in tests to compare generated tokens with the interpreter's tokens.
lexerDumpTokens(args: Array[Str]) () / []:
    if args.len() != 2:
        panic("USAGE: fir compiler/Lexer.fir --main lexerTestMain -- <file>")

    let file = args.get(1)
    let fileContents = readFileUtf8(file)
    let (tokens, error) = tokenize(file, fileContents)
    if error is Option.Some(error):
        print("ERROR: `error.loc.line + 1`:`error.loc.col + 1`: `error.msg`")
    for token: Token in tokens.iter():
        print("`token.line + 1`:`token.col + 1`: `token.kind`")


type Lexer:
    _file: Str
    _input: Str
    _byteIdx: U32
    _line: U32
    _col: U32


Lexer._fail(self, msg: Str) a / Error:
    throw(Error(loc = Loc(file = self._file, byteIdx = self._byteIdx, byteLen = 0, line = self._line, col = self._col), msg = msg))


# NB. Panics if OOB.
Lexer._nextChar(self) Char:
    self._input.charAt(self._byteIdx)


Lexer._next(self) Option[Token] / Error:
    # Skip whitespace and comments before actual tokens.
    loop:
        while self._byteIdx < self._input.len() and self._nextChar() is char and char.isAsciiWhitespace():
            self._byteIdx += 1
            if char == '\n':
                self._line += 1
                self._col = 0
            else:
                self._col += 1

        if self._byteIdx == self._input.len():
            return Option.None

        if self._nextChar() == '#':
            self._byteIdx += 1
            self._col += 1

            if self._byteIdx < self._input.len() and self._nextChar() == '|':
                self._byteIdx += 1
                self._col += 1
                self._skipMultiLineComment()
            else:
                self._skipSingleLineComment()

            continue

        break

    let byteIdx = self._byteIdx
    let line = self._line
    let col = self._col

    match self._input.substr(self._byteIdx, self._input.len()):
        # ------------------------------------------------------------------------------------------
        # Keywords

        "as" rest if not _isIdContStr(rest):
            self._byteIdx += 2
            self._col += 2
            return Option.Some(Token(kind = TokenKind.As, text = "as", byteIdx, line, col))

        "is" rest if not _isIdContStr(rest):
            self._byteIdx += 2
            self._col += 2
            return Option.Some(Token(kind = TokenKind.Is, text = "is", byteIdx, line, col))

        "break" rest if not _isIdContStr(rest):
            self._byteIdx += 5
            self._col += 5
            return Option.Some(Token(kind = TokenKind.Break, text = "break", byteIdx, line, col))

        "continue" rest if not _isIdContStr(rest):
            self._byteIdx += 8
            self._col += 8
            return Option.Some(Token(kind = TokenKind.Continue, text = "continue", byteIdx, line, col))

        "elif" rest if not _isIdContStr(rest):
            self._byteIdx += 4
            self._col += 4
            return Option.Some(Token(kind = TokenKind.Elif, text = "elif", byteIdx, line, col))

        "else" rest if not _isIdContStr(rest):
            self._byteIdx += 4
            self._col += 4
            return Option.Some(Token(kind = TokenKind.Else, text = "else", byteIdx, line, col))

        "export" rest if not _isIdContStr(rest):
            self._byteIdx += 6
            self._col += 6
            return Option.Some(Token(kind = TokenKind.Export, text = "export", byteIdx, line, col))

        "fn" rest if not _isIdContStr(rest):
            self._byteIdx += 2
            self._col += 2
            return Option.Some(Token(kind = TokenKind.Fn_, text = "fn", byteIdx, line, col))

        "Fn" rest if not _isIdContStr(rest):
            self._byteIdx += 2
            self._col += 2
            return Option.Some(Token(kind = TokenKind.UpperFn, text = "Fn", byteIdx, line, col))

        "for" rest if not _isIdContStr(rest):
            self._byteIdx += 3
            self._col += 3
            return Option.Some(Token(kind = TokenKind.For, text = "for", byteIdx, line, col))

        "if" rest if not _isIdContStr(rest):
            self._byteIdx += 2
            self._col += 2
            return Option.Some(Token(kind = TokenKind.If, text = "if", byteIdx, line, col))

        "impl" rest if not _isIdContStr(rest):
            self._byteIdx += 4
            self._col += 4
            return Option.Some(Token(kind = TokenKind.Impl, text = "impl", byteIdx, line, col))

        "import" rest if not _isIdContStr(rest):
            self._byteIdx += 6
            self._col += 6
            return Option.Some(Token(kind = TokenKind.Import, text = "import", byteIdx, line, col))

        "in" rest if not _isIdContStr(rest):
            self._byteIdx += 2
            self._col += 2
            return Option.Some(Token(kind = TokenKind.In, text = "in", byteIdx, line, col))

        "jump" rest if not _isIdContStr(rest):
            self._byteIdx += 4
            self._col += 4
            return Option.Some(Token(kind = TokenKind.Jump, text = "jump", byteIdx, line, col))

        "let" rest if not _isIdContStr(rest):
            self._byteIdx += 3
            self._col += 3
            return Option.Some(Token(kind = TokenKind.Let, text = "let", byteIdx, line, col))

        "match" rest if not _isIdContStr(rest):
            self._byteIdx += 5
            self._col += 5
            return Option.Some(Token(kind = TokenKind.Match, text = "match", byteIdx, line, col))

        "prim" rest if not _isIdContStr(rest):
            self._byteIdx += 4
            self._col += 4
            return Option.Some(Token(kind = TokenKind.Prim, text = "prim", byteIdx, line, col))

        "return" rest if not _isIdContStr(rest):
            self._byteIdx += 6
            self._col += 6
            return Option.Some(Token(kind = TokenKind.Return, text = "return", byteIdx, line, col))

        "trait" rest if not _isIdContStr(rest):
            self._byteIdx += 5
            self._col += 5
            return Option.Some(Token(kind = TokenKind.Trait, text = "trait", byteIdx, line, col))

        "type" rest if not _isIdContStr(rest):
            self._byteIdx += 4
            self._col += 4
            return Option.Some(Token(kind = TokenKind.Type, text = "type", byteIdx, line, col))

        "var" rest if not _isIdContStr(rest):
            self._byteIdx += 3
            self._col += 3
            return Option.Some(Token(kind = TokenKind.Var, text = "var", byteIdx, line, col))

        "while" rest if not _isIdContStr(rest):
            self._byteIdx += 5
            self._col += 5
            return Option.Some(Token(kind = TokenKind.While, text = "while", byteIdx, line, col))

        "do" rest if not _isIdContStr(rest):
            self._byteIdx += 2
            self._col += 2
            return Option.Some(Token(kind = TokenKind.Do, text = "Do", byteIdx, line, col))

        "loop" rest if not _isIdContStr(rest):
            self._byteIdx += 4
            self._col += 4
            return Option.Some(Token(kind = TokenKind.Loop, text = "Loop", byteIdx, line, col))

        "row(" _:
            self._byteIdx += 4
            self._col += 4
            return Option.Some(Token(kind = TokenKind.LParenRow, text = "row(", byteIdx, line, col))

        "row[" _:
            self._byteIdx += 4
            self._col += 4
            return Option.Some(Token(kind = TokenKind.LBracketRow, text = "row[", byteIdx, line, col))

        "not" rest if not _isIdContStr(rest):
            self._byteIdx += 3
            self._col += 3
            return Option.Some(Token(kind = TokenKind.Not, text = "not", byteIdx, line, col))

        # ------------------------------------------------------------------------------------------
        # Delimiters

        "(" _:
            self._byteIdx += 1
            self._col += 1
            return Option.Some(Token(kind = TokenKind.LParen, text = "(", byteIdx, line, col))

        ")" _:
            self._byteIdx += 1
            self._col += 1
            return Option.Some(Token(kind = TokenKind.RParen, text = ")", byteIdx, line, col))

        "[" _:
            self._byteIdx += 1
            self._col += 1
            return Option.Some(Token(kind = TokenKind.LBracket, text = "[", byteIdx, line, col))

        "]" _:
            self._byteIdx += 1
            self._col += 1
            return Option.Some(Token(kind = TokenKind.RBracket, text = "]", byteIdx, line, col))

        "{" _:
            self._byteIdx += 1
            self._col += 1
            return Option.Some(Token(kind = TokenKind.LBrace, text = "{", byteIdx, line, col))

        "}" _:
            self._byteIdx += 1
            self._col += 1
            return Option.Some(Token(kind = TokenKind.RBrace, text = "}", byteIdx, line, col))

        # ------------------------------------------------------------------------------------------
        # Punctuation

        "," _:
            self._byteIdx += 1
            self._col += 1
            return Option.Some(Token(kind = TokenKind.Comma, text = ",", byteIdx, line, col))

        ":" _:
            self._byteIdx += 1
            self._col += 1
            return Option.Some(Token(kind = TokenKind.Colon, text = ":", byteIdx, line, col))

        ".." _:
            self._byteIdx += 2
            self._col += 2
            return Option.Some(Token(kind = TokenKind.DotDot, text = "..", byteIdx, line, col))

        "." _:
            self._byteIdx += 1
            self._col += 1
            return Option.Some(Token(kind = TokenKind.Dot, text = ".", byteIdx, line, col))

        "_" rest if not _isIdContStr(rest):
            self._byteIdx += 1
            self._col += 1
            return Option.Some(Token(kind = TokenKind.Underscore, text = "_", byteIdx, line, col))

        # ------------------------------------------------------------------------------------------
        # Operators

        "==" _:
            self._byteIdx += 2
            self._col += 2
            return Option.Some(Token(kind = TokenKind.EqEq, text = "==", byteIdx, line, col))

        "=" _:
            self._byteIdx += 1
            self._col += 1
            return Option.Some(Token(kind = TokenKind.Eq, text = "=", byteIdx, line, col))

        "+=" _:
            self._byteIdx += 2
            self._col += 2
            return Option.Some(Token(kind = TokenKind.PlusEq, text = "+=", byteIdx, line, col))

        "-=" _:
            self._byteIdx += 2
            self._col += 2
            return Option.Some(Token(kind = TokenKind.MinusEq, text = "-=", byteIdx, line, col))

        "*=" _:
            self._byteIdx += 2
            self._col += 2
            return Option.Some(Token(kind = TokenKind.StarEq, text = "*=", byteIdx, line, col))

        "^=" _:
            self._byteIdx += 2
            self._col += 2
            return Option.Some(Token(kind = TokenKind.CaretEq, text = "*=", byteIdx, line, col))

        "+" _:
            self._byteIdx += 1
            self._col += 1
            return Option.Some(Token(kind = TokenKind.Plus, text = "+", byteIdx, line, col))

        # TODO: Handle negative numbers here by checking whether `rest` starts with a digit.
        "-" rest:
            self._byteIdx += 1
            self._col += 1
            return Option.Some(Token(kind = TokenKind.Minus, text = "-", byteIdx, line, col))

        "*" _:
            self._byteIdx += 1
            self._col += 1
            return Option.Some(Token(kind = TokenKind.Star, text = "*", byteIdx, line, col))

        "!=" _:
            self._byteIdx += 2
            self._col += 2
            return Option.Some(Token(kind = TokenKind.ExclamationEq, text = "!=", byteIdx, line, col))

        "!" _:
            self._byteIdx += 1
            self._col += 1
            return Option.Some(Token(kind = TokenKind.Exclamation, text = "!", byteIdx, line, col))

        "and" _:
            self._byteIdx += 3
            self._col += 3
            return Option.Some(Token(kind = TokenKind.And, text = "and", byteIdx, line, col))

        "&&" _:
            self._byteIdx += 2
            self._col += 2
            return Option.Some(Token(kind = TokenKind.AmpAmp, text = "&&", byteIdx, line, col))

        "&" _:
            self._byteIdx += 1
            self._col += 1
            return Option.Some(Token(kind = TokenKind.Amp, text = "&", byteIdx, line, col))

        "or" _:
            self._byteIdx += 2
            self._col += 2
            return Option.Some(Token(kind = TokenKind.Or, text = "or", byteIdx, line, col))

        "||" _:
            self._byteIdx += 2
            self._col += 2
            return Option.Some(Token(kind = TokenKind.PipePipe, text = "||", byteIdx, line, col))

        "|" _:
            self._byteIdx += 1
            self._col += 1
            return Option.Some(Token(kind = TokenKind.Pipe, text = "|", byteIdx, line, col))

        "<<" _:
            self._byteIdx += 2
            self._col += 2
            return Option.Some(Token(kind = TokenKind.DoubleLAngle, text = "<<", byteIdx, line, col))

        "<=" _:
            self._byteIdx += 2
            self._col += 2
            return Option.Some(Token(kind = TokenKind.LAngleEq, text = "<=", byteIdx, line, col))

        "<" _:
            self._byteIdx += 1
            self._col += 1
            return Option.Some(Token(kind = TokenKind.LAngle, text = "<", byteIdx, line, col))

        ">>" _:
            self._byteIdx += 2
            self._col += 2
            return Option.Some(Token(kind = TokenKind.DoubleRAngle, text = ">>", byteIdx, line, col))

        ">=" _:
            self._byteIdx += 2
            self._col += 2
            return Option.Some(Token(kind = TokenKind.RAngleEq, text = ">=", byteIdx, line, col))

        ">" _:
            self._byteIdx += 1
            self._col += 1
            return Option.Some(Token(kind = TokenKind.RAngle, text = ">", byteIdx, line, col))

        "/" _:
            self._byteIdx += 1
            self._col += 1
            return Option.Some(Token(kind = TokenKind.Slash, text = "/", byteIdx, line, col))

        "\\" _:
            self._byteIdx += 1
            self._col += 1
            return Option.Some(Token(kind = TokenKind.Backslash, text = "\\", byteIdx, line, col))

        "?" _:
            self._byteIdx += 1
            self._col += 1
            return Option.Some(Token(kind = TokenKind.Question, text = "?", byteIdx, line, col))

        # ------------------------------------------------------------------------------------------
        # Literals

        "\"" _:
            return Option.Some(self._string())

        "'" _:
            return Option.Some(self._char())

        "0b" _:
            let digitsStart = self._byteIdx
            self._byteIdx += 2
            self._col += 2

            while self._byteIdx < self._input.len():
                let c = self._nextChar()
                if c != '_' and not c.isAsciiBinDigit():
                    break
                self._byteIdx += 1
                self._col += 1

            return Option.Some(Token(
                kind = TokenKind.BinInt,
                text = self._input.substr(digitsStart, self._byteIdx),
                byteIdx = digitsStart,
                line,
                col,
            ))

        "0x" _:
            let digitsStart = self._byteIdx
            self._byteIdx += 2
            self._col += 2

            while self._byteIdx < self._input.len():
                let c = self._nextChar()
                if c != '_' and not c.isAsciiHexDigit():
                    break
                self._byteIdx += 1
                self._col += 1

            return Option.Some(Token(
                kind = TokenKind.HexInt,
                text = self._input.substr(digitsStart, self._byteIdx),
                byteIdx = digitsStart,
                line,
                col,
            ))

        # ------------------------------------------------------------------------------------------

        "~" _:
            let idStart = self._byteIdx
            self._byteIdx += 1
            self._col += 1
            if self._byteIdx < self._input.len() and self._nextChar().isAsciiUppercase():
                self._byteIdx += 1
                self._col += 1
                while self._byteIdx < self._input.len() and _isIdCont(self._nextChar()):
                    self._byteIdx += 1
                    self._col += 1
                return Option.Some(Token(
                    kind = TokenKind.TildeUpperId,
                    text = self._input.substr(idStart, self._byteIdx),
                    byteIdx,
                    line,
                    col
                ))
            else:
                return Option.Some(Token(
                    kind = TokenKind.Tilde,
                    text = "~",
                    byteIdx,
                    line,
                    col,
                ))

        _:
            let c = self._nextChar()

            if c.isAsciiDigit():
                let digitsStart = self._byteIdx
                self._byteIdx += 1
                self._col += 1

                while self._byteIdx < self._input.len():
                    let c = self._nextChar()
                    if c != '_' and not c.isAsciiDigit():
                        break
                    self._byteIdx += 1
                    self._col += 1

                return Option.Some(Token(
                    kind = TokenKind.Int,
                    text = self._input.substr(digitsStart, self._byteIdx),
                    byteIdx,
                    line,
                    col,
                ))

            # If the rest starts with '_' then there must be an identifier char after it, as the
            # other case is handled above. This character specifies the casing.
            let caseCheckIdx = self._byteIdx
            while caseCheckIdx < self._input.len() and self._input.charAt(caseCheckIdx) == '_':
                caseCheckIdx += 1

            if caseCheckIdx == self._input.len():
                panic("`line + 1`:`col + 1`: Unexpected end of input")

            let caseCheckChar = self._input.charAt(caseCheckIdx)
            let uppercaseId = caseCheckChar.isAsciiUppercase()
            let lowercaseId = caseCheckChar.isAsciiLowercase()

            if uppercaseId or lowercaseId:
                let endIdx = self._byteIdx + 1
                self._col += 1
                while self._input.len() > endIdx and _isIdCont(self._input.charAt(endIdx)):
                    endIdx += 1
                    self._col += 1
                let id = self._input.substr(self._byteIdx, endIdx)
                let kind = if uppercaseId:
                    TokenKind.UpperId
                else:
                    TokenKind.LowerId
                self._byteIdx = endIdx
                return Option.Some(Token(
                    kind,
                    text = id,
                    byteIdx,
                    line,
                    col,
                ))

            panic("TODO: `c` at `line + 1`:`col + 1`")


# NB. Initial '"' should NOT be consumed.
Lexer._string(self) Token / Error:
    let startIdx = self._byteIdx
    let startLine = self._line
    let startCol = self._col
    self._byteIdx += 1 # Skip initial '#'
    self._col += 1
    while self._byteIdx < self._input.len():
        match self._nextChar():
            '"':
                self._byteIdx += 1
                self._col += 1
                return Token(
                    kind = TokenKind.Str,
                    text = self._input.substr(startIdx, self._byteIdx),
                    byteIdx = startIdx,
                    line = startLine,
                    col = startCol,
                )

            '`':
                # TODO: Allow nesting.
                # Nesting needs to be handled in coordination with the parser,
                # as the lexer cannot (or should not) keep track of the brackets
                # and maintain a tree structure.
                # This means we won't be able to tokenize files without the help.
                self._byteIdx += 1
                self._col += 1
                while self._byteIdx < self._input.len():
                    match self._nextChar():
                        '`':
                            self._byteIdx += 1
                            self._col += 1
                            break

                        _:
                            self._byteIdx += 1
                            self._col += 1

            '\\':
                self._byteIdx += 1
                self._col += 1
                match self._nextChar():
                    '`' | '"' | 'n' | 't' | 'r' | '\\':
                        self._byteIdx += 1
                        self._col += 1
                    other:
                        self._fail("invalid escape: '`other`'")

            other:
                self._byteIdx += other.lenUtf8()

                # TODO: Handle non-ascii
                self._col += other.lenUtf8()

    self._fail("unterminated string literal")


# NB. Initial '\'' should NOT be consumed.
Lexer._char(self) Token / Error:
    let idx = self._byteIdx
    let line = self._line
    let col = self._col

    self._byteIdx += 1
    self._col += 1
    let char = match self._nextChar():
        '\\':
            self._byteIdx += 1
            self._col += 1
            match self._nextChar():
                '\'': '\''
                '\\': '\\'
                'n': '\n'
                't': '\t'
                'r': '\r'
                other: self._fail("invalid escape character in character literal: '`other`'")
        c: c
    self._byteIdx += char.lenUtf8()
    self._col += char.lenUtf8()         # TODO: Handle non-ascii
    if self._nextChar() != '\'':
        self._fail("unterminated character literal")

    self._byteIdx += 1
    self._col += 1
    Token(kind = TokenKind.Char, text = self._input.substr(idx, self._byteIdx), byteIdx = idx, line, col)


Lexer._skipSingleLineComment(self):
    while self._byteIdx < self._input.len():
        let c = self._nextChar()
        self._byteIdx += c.lenUtf8()
        if c == '\n':
            self._col = 0
            self._line += 1
            return
        self._col += c.lenUtf8()         # TODO: Handle non-ascii


Lexer._skipMultiLineComment(self) () / Error:
    while self._byteIdx < self._input.len():
        let c = self._nextChar()
        self._byteIdx += c.lenUtf8()
        self._col += c.lenUtf8()        # TODO: Handle non-ascii
        if c == '|':
            if self._byteIdx < self._input.len():
                let c = self._nextChar()
                if c == '#':
                    self._byteIdx += 1
                    self._col += 1
                    return

    self._fail("unterminated multi-line comment")


_isIdCont(c: Char) Bool:
    c.isAsciiAlphanumeric() or c == '_'


_isIdContStr(s: Str) Bool:
    match s.chars().next():
        Option.Some(c): _isIdCont(c)
        Option.None: Bool.False
