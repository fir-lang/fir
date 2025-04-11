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

impl ToStr[Token]:
    toStr(self: Token): Str
        "`self.kind.toStr()`(`self.byteIdx.toStr()`, \"`self.text`\")"

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

impl ToStr[IntKind]:
    toStr(self: IntKind): Str
        match self:
            IntKind.I8: "I8"
            IntKind.U8: "U8"
            IntKind.I32: "I32"
            IntKind.U32: "U32"