type Token:
    kind: TokenKind
    text: Str
    byteIdx: U32
    line: U32
    col: U32


Token.rightLoc(self) (line: U32, col: U32):
    let line = self.line
    let col = self.col
    for c: Char in self.text.chars():
        if c == '\n':
            line += 1
            col = 0
        else:
            col += 1
    (line = line, col = col)


type TokenKind:
    # An identifier starting with an uppercase letter.
    UpperId

    # `UpperId '.' UpperId`, without spaces in between.
    UpperIdPath

    # An identifier starting with an uppercase letter, followed by a '.['.
    #
    # This starts an iterator syntax.
    #
    # NOTE: This is only used when comparing scanner-generated tokens with the interpreter's tokens.
    # We will be removed once we have our own tests.
    UpperIdDotLBracket

    # An identifier starting with '~', followed by an uppercase letter.
    #
    # NOTE: '~' followed by an uppercase letter is tokenized as one in the interpreter, and we do
    # the same here to be able to compare interpreter's and compiler's tokens when testing. We don't
    # need to combine them in the compiler. We will remove this once we have our own tests.
    TildeUpperId

    # `'~' UpperId '.' UpperId`, without spaces in between.
    #
    # NOTE: This is only used when comparing scanner-generated tokens with the interpreter's tokens.
    # It will be removed once we have our own tests.
    TildeUpperIdPath

    # An identifier starting with a lowercase letter.
    LowerId

    # Keywords
    And
    As
    Break
    Continue
    Do
    Elif
    Else
    Export
    Fn_
    For
    If
    Impl
    Import
    In
    Is
    Jump
    Let
    Loop
    Match
    Not
    Or
    Prim
    Return
    Trait
    Type
    UpperFn
    Var
    While

    # Delimiters
    LBrace
    LBracket
    LBracketRow
    LParen
    LParenRow
    RBrace
    RBracket
    RParen
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
    CaretEq
    Dollar
    DotDot
    DoubleLAngle
    DoubleRAngle
    Eq
    EqEq
    Exclamation
    ExclamationEq
    LAngle
    LAngleEq
    Minus
    MinusEq
    Pipe
    PipePipe
    Plus
    PlusEq
    Question
    RAngle
    RAngleEq
    Slash
    Star
    StarEq
    Tilde

    # Literals
    Str
    Int
    HexInt
    BinInt
    Char

    # Indentation
    Newline
    Indent
    Dedent

    Label

type IntKind:
    I8
    U8
    I32
    U32

impl ToStr[Token]:
    toStr(self: Token) Str:
        let text = if self.kind is TokenKind.Str | TokenKind.Newline | TokenKind.Indent:
            _escape(self.text)
        else:
            self.text

        "`self.kind`(`self.line + 1`:`self.col + 1`:\"`text`\")"

_escape(s: Str) Str:
    let buf = StrBuf.withCapacity(s.len() + 10)

    for char: Char in s.chars():
        match char:
            '"':
                buf.push('\\')
                buf.push('"')
            '\n':
                buf.push('\\')
                buf.push('n')
            '\t':
                buf.push('\\')
                buf.push('t')
            '\r':
                buf.push('\\')
                buf.push('r')
            '\\':
                buf.push('\\')
                buf.push('\\')
            other:
                buf.push(other)
    buf.toStr()

impl ToStr[TokenKind]:
    toStr(self: TokenKind) Str:
        match self:
            TokenKind.Amp: "Amp"
            TokenKind.AmpAmp: "&&"
            TokenKind.And: "And"
            TokenKind.As: "As"
            TokenKind.Backslash: "Backslash"
            TokenKind.BinInt: "BinInt"
            TokenKind.Break: "Break"
            TokenKind.CaretEq: "CaretEq"
            TokenKind.Char: "Char"
            TokenKind.Colon: "Colon"
            TokenKind.Comma: "Comma"
            TokenKind.Continue: "Continue"
            TokenKind.Dedent: "Dedent"
            TokenKind.Do: "Do"
            TokenKind.Dollar: "$"
            TokenKind.Dot: "Dot"
            TokenKind.DotDot: "DotDot"
            TokenKind.DoubleLAngle: "DoubleLAngle"
            TokenKind.DoubleRAngle: "DoubleRAngle"
            TokenKind.Elif: "Elif"
            TokenKind.Else: "Else"
            TokenKind.Eq: "Eq"
            TokenKind.EqEq: "EqEq"
            TokenKind.Exclamation: "Exclamation"
            TokenKind.ExclamationEq: "ExclamationEq"
            TokenKind.Export: "Export"
            TokenKind.Fn_: "Fn"
            TokenKind.For: "For"
            TokenKind.HexInt: "HexInt"
            TokenKind.If: "If"
            TokenKind.Impl: "Impl"
            TokenKind.Import: "Import"
            TokenKind.In: "In"
            TokenKind.Indent: "Indent"
            TokenKind.Int: "Int"
            TokenKind.Is: "Is"
            TokenKind.Jump: "Jump"
            TokenKind.Label: "Label"
            TokenKind.LAngle: "LAngle"
            TokenKind.LAngleEq: "LAngleEq"
            TokenKind.LBrace: "LBrace"
            TokenKind.LBracket: "LBracket"
            TokenKind.LBracketRow: "LBracketRow"
            TokenKind.Let: "Let"
            TokenKind.Loop: "Loop"
            TokenKind.LowerId: "LowerId"
            TokenKind.LParen: "LParen"
            TokenKind.LParenRow: "LParenRow"
            TokenKind.Match: "Match"
            TokenKind.Minus: "Minus"
            TokenKind.MinusEq: "MinusEq"
            TokenKind.Newline: "Newline"
            TokenKind.Not: "Not"
            TokenKind.Or: "Or"
            TokenKind.Pipe: "Pipe"
            TokenKind.PipePipe: "PipePipe"
            TokenKind.Plus: "Plus"
            TokenKind.PlusEq: "PlusEq"
            TokenKind.Prim: "Prim"
            TokenKind.Question: "Question"
            TokenKind.RAngle: "RAngle"
            TokenKind.RAngleEq: "RAngleEq"
            TokenKind.RBrace: "RBrace"
            TokenKind.RBracket: "RBracket"
            TokenKind.Return: "Return"
            TokenKind.RParen: "RParen"
            TokenKind.SingleQuote: "SingleQuote"
            TokenKind.Slash: "Slash"
            TokenKind.Star: "Star"
            TokenKind.StarEq: "StarEq"
            TokenKind.Str: "Str"
            TokenKind.Tilde: "Tilde"
            TokenKind.TildeUpperId: "TildeUpperId"
            TokenKind.TildeUpperIdPath: "TildeUpperIdPath"
            TokenKind.Trait: "Trait"
            TokenKind.Type: "Type"
            TokenKind.Underscore: "Underscore"
            TokenKind.UpperFn: "UpperFn"
            TokenKind.UpperId: "UpperId"
            TokenKind.UpperIdDotLBracket: "UpperIdDotLBracket"
            TokenKind.UpperIdPath: "UpperIdPath"
            TokenKind.Var: "Var"
            TokenKind.While: "While"

impl Eq[TokenKind]:
    __eq(self: TokenKind, other: TokenKind) Bool:
        match (left = self, right = other):
            (left = TokenKind.Amp, right = TokenKind.Amp): Bool.True
            (left = TokenKind.And, right = TokenKind.And): Bool.True
            (left = TokenKind.As, right = TokenKind.As): Bool.True
            (left = TokenKind.Backslash, right = TokenKind.Backslash): Bool.True
            (left = TokenKind.BinInt, right = TokenKind.BinInt): Bool.True
            (left = TokenKind.Break, right = TokenKind.Break): Bool.True
            (left = TokenKind.Char, right = TokenKind.Char): Bool.True
            (left = TokenKind.Colon, right = TokenKind.Colon): Bool.True
            (left = TokenKind.Comma, right = TokenKind.Comma): Bool.True
            (left = TokenKind.Continue, right = TokenKind.Continue): Bool.True
            (left = TokenKind.Dedent, right = TokenKind.Dedent): Bool.True
            (left = TokenKind.Do, right = TokenKind.Do): Bool.True
            (left = TokenKind.Dollar, right = TokenKind.Dollar): Bool.True
            (left = TokenKind.Dot, right = TokenKind.Dot): Bool.True
            (left = TokenKind.DotDot, right = TokenKind.DotDot): Bool.True
            (left = TokenKind.DoubleLAngle, right = TokenKind.DoubleLAngle): Bool.True
            (left = TokenKind.DoubleRAngle, right = TokenKind.DoubleRAngle): Bool.True
            (left = TokenKind.Elif, right = TokenKind.Elif): Bool.True
            (left = TokenKind.Else, right = TokenKind.Else): Bool.True
            (left = TokenKind.Eq, right = TokenKind.Eq): Bool.True
            (left = TokenKind.EqEq, right = TokenKind.EqEq): Bool.True
            (left = TokenKind.Exclamation, right = TokenKind.Exclamation): Bool.True
            (left = TokenKind.ExclamationEq, right = TokenKind.ExclamationEq): Bool.True
            (left = TokenKind.Export, right = TokenKind.Export): Bool.True
            (left = TokenKind.Fn_, right = TokenKind.Fn_): Bool.True
            (left = TokenKind.For, right = TokenKind.For): Bool.True
            (left = TokenKind.HexInt, right = TokenKind.HexInt): Bool.True
            (left = TokenKind.If, right = TokenKind.If): Bool.True
            (left = TokenKind.Impl, right = TokenKind.Impl): Bool.True
            (left = TokenKind.Import, right = TokenKind.Import): Bool.True
            (left = TokenKind.In, right = TokenKind.In): Bool.True
            (left = TokenKind.Indent, right = TokenKind.Indent): Bool.True
            (left = TokenKind.Int, right = TokenKind.Int): Bool.True
            (left = TokenKind.Jump, right = TokenKind.Jump): Bool.True
            (left = TokenKind.Label, right = TokenKind.Label): Bool.True
            (left = TokenKind.LAngle, right = TokenKind.LAngle): Bool.True
            (left = TokenKind.LAngleEq, right = TokenKind.LAngleEq): Bool.True
            (left = TokenKind.LBrace, right = TokenKind.LBrace): Bool.True
            (left = TokenKind.LBracket, right = TokenKind.LBracket): Bool.True
            (left = TokenKind.LBracketRow, right = TokenKind.LBracketRow): Bool.True
            (left = TokenKind.Let, right = TokenKind.Let): Bool.True
            (left = TokenKind.Loop, right = TokenKind.Loop): Bool.True
            (left = TokenKind.LowerId, right = TokenKind.LowerId): Bool.True
            (left = TokenKind.LParen, right = TokenKind.LParen): Bool.True
            (left = TokenKind.LParenRow, right = TokenKind.LParenRow): Bool.True
            (left = TokenKind.Match, right = TokenKind.Match): Bool.True
            (left = TokenKind.Minus, right = TokenKind.Minus): Bool.True
            (left = TokenKind.MinusEq, right = TokenKind.MinusEq): Bool.True
            (left = TokenKind.Newline, right = TokenKind.Newline): Bool.True
            (left = TokenKind.Not, right = TokenKind.Not): Bool.True
            (left = TokenKind.Or, right = TokenKind.Or): Bool.True
            (left = TokenKind.Pipe, right = TokenKind.Pipe): Bool.True
            (left = TokenKind.PipePipe, right = TokenKind.PipePipe): Bool.True
            (left = TokenKind.Plus, right = TokenKind.Plus): Bool.True
            (left = TokenKind.PlusEq, right = TokenKind.PlusEq): Bool.True
            (left = TokenKind.Prim, right = TokenKind.Prim): Bool.True
            (left = TokenKind.RAngle, right = TokenKind.RAngle): Bool.True
            (left = TokenKind.RAngleEq, right = TokenKind.RAngleEq): Bool.True
            (left = TokenKind.RBrace, right = TokenKind.RBrace): Bool.True
            (left = TokenKind.RBracket, right = TokenKind.RBracket): Bool.True
            (left = TokenKind.Return, right = TokenKind.Return): Bool.True
            (left = TokenKind.RParen, right = TokenKind.RParen): Bool.True
            (left = TokenKind.SingleQuote, right = TokenKind.SingleQuote): Bool.True
            (left = TokenKind.Slash, right = TokenKind.Slash): Bool.True
            (left = TokenKind.Star, right = TokenKind.Star): Bool.True
            (left = TokenKind.StarEq, right = TokenKind.StarEq): Bool.True
            (left = TokenKind.Str, right = TokenKind.Str): Bool.True
            (left = TokenKind.Tilde, right = TokenKind.Tilde): Bool.True
            (left = TokenKind.TildeUpperId, right = TokenKind.TildeUpperId): Bool.True
            (left = TokenKind.TildeUpperIdPath, right = TokenKind.TildeUpperIdPath): Bool.True
            (left = TokenKind.Trait, right = TokenKind.Trait): Bool.True
            (left = TokenKind.Type, right = TokenKind.Type): Bool.True
            (left = TokenKind.Underscore, right = TokenKind.Underscore): Bool.True
            (left = TokenKind.UpperFn, right = TokenKind.UpperFn): Bool.True
            (left = TokenKind.UpperId, right = TokenKind.UpperId): Bool.True
            (left = TokenKind.UpperIdDotLBracket, right = TokenKind.UpperIdDotLBracket): Bool.True
            (left = TokenKind.UpperIdPath, right = TokenKind.UpperIdPath): Bool.True
            (left = TokenKind.Var, right = TokenKind.Var): Bool.True
            (left = TokenKind.While, right = TokenKind.While): Bool.True
            _: Bool.False

impl Eq[IntKind]:
    __eq(self: IntKind, other: IntKind) Bool:
        match (left = self, right = other):
            (left = IntKind.I8, right = IntKind.I8): Bool.True
            (left = IntKind.U8, right = IntKind.U8): Bool.True
            (left = IntKind.I32, right = IntKind.I32): Bool.True
            (left = IntKind.U32, right = IntKind.U32): Bool.True
