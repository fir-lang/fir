# A self lexer.

type Token:
    kind: TokenKind
    text: Str

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
    Int:
        kind: Option[IntKind]
    HexInt:
        kind: Option[IntKind]
    BinInt:
        kind: Option[IntKind]
    Char

type IntKind:
    I8
    U8
    I32
    U32

fn tokenize(input: Str): Vec[Token] =
    Vec.withCapacity(123)
    # let input = skipTrivia(input)

fn tokenize_(input: Str, byteIdx: U32, tokens: Vec[Token]) =
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

        ()
    ()

fn skipMultiLineComment(input: Str, byteIdx: U32): U32 =
    while byteIdx < input.len():
        let c = input.charAt(byteIdx)
        byteIdx += 1
        if c == '|':
            if byteIdx < input.len():
                let c = input.charAt(byteIdx)
                if c == '#':
                    return byteIdx + 1

    panic("Unterminated multi-line comment")

fn skipSingleLineComment(input: Str, byteIdx: U32): U32 =
    while byteIdx < input.len():
        let c = input.charAt(byteIdx)
        byteIdx += 1
        if c == '\n':
            break

    byteIdx

fn main() = ()
