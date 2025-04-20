type Token:
    kind: TokenKind
    text: Str
    byteIdx: U32

type TokenKind:
    # An identifier starting with an uppercase letter.
    UpperId

    # An identifier starting with '~', followed by an uppercase letter.
    TildeUpperId

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
    RAngle
    RAngleEq
    Slash
    Star
    StarEq
    Tilde

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
            TokenKind.Amp: "Amp"
            TokenKind.AmpAmp: "AmpAmp"
            TokenKind.As: "As"
            TokenKind.Backslash: "Backslash"
            TokenKind.BinInt(kind): "BinInt(`kind.toStr()`)"
            TokenKind.Break: "Break"
            TokenKind.Char(char): "Char(`char.toStr()`)"
            TokenKind.Colon: "Colon"
            TokenKind.Comma: "Comma"
            TokenKind.Continue: "Continue"
            TokenKind.Dot: "Dot"
            TokenKind.DotDot: "DotDot"
            TokenKind.DotDotEq: "DotDotEq"
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
            TokenKind.HexInt(kind): "HexInt(`kind.toStr()`)"
            TokenKind.If: "If"
            TokenKind.Impl: "Impl"
            TokenKind.Import: "Import"
            TokenKind.In: "In"
            TokenKind.Int(kind): "Int(`kind.toStr()`)"
            TokenKind.Jump: "Jump"
            TokenKind.LAngle: "LAngle"
            TokenKind.LAngleEq: "LAngleEq"
            TokenKind.LBrace: "LBrace"
            TokenKind.LBracket: "LBracket"
            TokenKind.LParen: "LParen"
            TokenKind.Let: "Let"
            TokenKind.LowerId: "LowerId"
            TokenKind.Match: "Match"
            TokenKind.Minus: "Minus"
            TokenKind.MinusEq: "MinusEq"
            TokenKind.Pipe: "Pipe"
            TokenKind.PipePipe: "PipePipe"
            TokenKind.Plus: "Plus"
            TokenKind.PlusEq: "PlusEq"
            TokenKind.Prim: "Prim"
            TokenKind.RAngle: "RAngle"
            TokenKind.RAngleEq: "RAngleEq"
            TokenKind.RBrace: "RBrace"
            TokenKind.RBracket: "RBracket"
            TokenKind.RParen: "RParen"
            TokenKind.Return: "Return"
            TokenKind.Self_: "Self"
            TokenKind.SingleQuote: "SingleQuote"
            TokenKind.Slash: "Slash"
            TokenKind.Star: "Star"
            TokenKind.StarEq: "StarEq"
            TokenKind.String: "String"
            TokenKind.TildeUpperId: "TildeUpperId"
            TokenKind.Trait: "Trait"
            TokenKind.Type: "Type"
            TokenKind.Underscore: "Underscore"
            TokenKind.UpperFn: "UpperFn"
            TokenKind.UpperId: "UpperId"
            TokenKind.Var: "Var"
            TokenKind.While: "While"

impl ToStr[IntKind]:
    toStr(self: IntKind): Str
        match self:
            IntKind.I8: "I8"
            IntKind.U8: "U8"
            IntKind.I32: "I32"
            IntKind.U32: "U32"
