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
    let tokens = Vec.withCapacity(1000)
    tokenize_(input, 0, tokens)
    tokens

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

        match input.substr(byteIdx, input.len()):
            ########################################################################################
            # Keywords

            "as" rest:
                tokens.push(Token(kind = TokenKind.As, text = "as"))
                byteIdx += 2

            "break" rest:
                tokens.push(Token(kind = TokenKind.Break, text = "break"))
                byteIdx += 5

            "continue" rest:
                tokens.push(Token(kind = TokenKind.Continue, text = "continue"))
                byteIdx += 8

            "elif" rest:
                tokens.push(Token(kind = TokenKind.Elif, text = "elif"))
                byteIdx += 4

            "else" rest:
                tokens.push(Token(kind = TokenKind.Else, text = "else"))
                byteIdx += 4

            "export" rest:
                tokens.push(Token(kind = TokenKind.Export, text = "export"))
                byteIdx += 6

            "fn" rest:
                tokens.push(Token(kind = TokenKind.Fn_, text = "fn"))
                byteIdx += 2

            "Fn" rest:
                tokens.push(Token(kind = TokenKind.UpperFn, text = "Fn"))
                byteIdx += 2

            "for" rest:
                tokens.push(Token(kind = TokenKind.For, text = "for"))
                byteIdx += 3

            "if" rest:
                tokens.push(Token(kind = TokenKind.If, text = "if"))
                byteIdx += 2

            "impl" rest:
                tokens.push(Token(kind = TokenKind.Impl, text = "impl"))
                byteIdx += 4

            "import" rest:
                tokens.push(Token(kind = TokenKind.Import, text = "import"))
                byteIdx += 6

            "in" rest:
                tokens.push(Token(kind = TokenKind.In, text = "in"))
                byteIdx += 2

            "jump" rest:
                tokens.push(Token(kind = TokenKind.Jump, text = "jump"))
                byteIdx += 4

            "let" rest:
                tokens.push(Token(kind = TokenKind.Let, text = "let"))
                byteIdx += 3

            "match" rest:
                tokens.push(Token(kind = TokenKind.Match, text = "match"))
                byteIdx += 5

            "prim" rest:
                tokens.push(Token(kind = TokenKind.Prim, text = "prim"))
                byteIdx += 4

            "return" rest:
                tokens.push(Token(kind = TokenKind.Return, text = "return"))
                byteIdx += 6

            "self" rest:
                tokens.push(Token(kind = TokenKind.Self_, text = "self"))
                byteIdx += 4

            "trait" rest:
                tokens.push(Token(kind = TokenKind.Trait, text = "trait"))
                byteIdx += 5

            "type" rest:
                tokens.push(Token(kind = TokenKind.Type, text = "type"))
                byteIdx += 4

            "var" rest:
                tokens.push(Token(kind = TokenKind.Var, text = "var"))
                byteIdx += 3

            "while" rest:
                tokens.push(Token(kind = TokenKind.While, text = "while"))
                byteIdx += 5

            ########################################################################################
            # Delimiters

            "(" rest:
                tokens.push(Token(kind = TokenKind.LParen, text = "("))
                byteIdx += 1

            ")" rest:
                tokens.push(Token(kind = TokenKind.RParen, text = ")"))
                byteIdx += 1

            "[" rest:
                tokens.push(Token(kind = TokenKind.LBracket, text = "["))
                byteIdx += 1

            "]" rest:
                tokens.push(Token(kind = TokenKind.RBracket, text = "]"))
                byteIdx += 1

            "{" rest:
                tokens.push(Token(kind = TokenKind.LBrace, text = "{"))
                byteIdx += 1

            "}" rest:
                tokens.push(Token(kind = TokenKind.RBrace, text = "}"))
                byteIdx += 1

            ########################################################################################
            # Punctuation

            "." rest:
                tokens.push(Token(kind = TokenKind.Dot, text = "."))
                byteIdx += 1

            "," rest:
                tokens.push(Token(kind = TokenKind.Comma, text = ","))
                byteIdx += 1

            ":" rest:
                tokens.push(Token(kind = TokenKind.Colon, text = ":"))
                byteIdx += 1

            # "\\" rest:
            #     tokens.push(Token(kind = TokenKind.Backslash, text = "\\"))
            #     byteIdx += 1

            "..=" rest:
                tokens.push(Token(kind = TokenKind.DotDotEq, text = "..="))
                byteIdx += 1

            ".." rest:
                tokens.push(Token(kind = TokenKind.DotDot, text = ".."))
                byteIdx += 1

            ########################################################################################
            # Operators

            "==" rest:
                tokens.push(Token(kind = TokenKind.EqEq, text = "=="))
                byteIdx += 2

            "=" rest:
                tokens.push(Token(kind = TokenKind.Eq, text = "="))
                byteIdx += 1

            "+=" rest:
                tokens.push(Token(kind = TokenKind.PlusEq, text = "+="))
                byteIdx += 2

            "-=" rest:
                tokens.push(Token(kind = TokenKind.MinusEq, text = "-="))
                byteIdx += 2

            "*=" rest:
                tokens.push(Token(kind = TokenKind.StarEq, text = "*="))
                byteIdx += 2

            "+" rest:
                tokens.push(Token(kind = TokenKind.Plus, text = "+"))
                byteIdx += 1

            "-" rest:
                tokens.push(Token(kind = TokenKind.Minus, text = "-"))
                byteIdx += 1

            "*" rest:
                tokens.push(Token(kind = TokenKind.Star, text = "*"))
                byteIdx += 1

            "!=" rest:
                tokens.push(Token(kind = TokenKind.ExclamationEq, text = "!="))
                byteIdx += 2

            "!" rest:
                tokens.push(Token(kind = TokenKind.Exclamation, text = "!"))
                byteIdx += 1

            "&&" rest:
                tokens.push(Token(kind = TokenKind.AmpAmp, text = "&&"))
                byteIdx += 2

            "&" rest:
                tokens.push(Token(kind = TokenKind.Amp, text = "&"))
                byteIdx += 1

            "||" rest:
                tokens.push(Token(kind = TokenKind.PipePipe, text = "||"))
                byteIdx += 2

            "|" rest:
                tokens.push(Token(kind = TokenKind.PipePipe, text = "|"))
                byteIdx += 1

            "<<" rest:
                tokens.push(Token(kind = TokenKind.DoubleLAngle, text = "<<"))
                byteIdx += 2

            "<=" rest:
                tokens.push(Token(kind = TokenKind.LAngleEq, text = "<="))
                byteIdx += 2

            "<" rest:
                tokens.push(Token(kind = TokenKind.LAngle, text = "<"))
                byteIdx += 1

            ">>" rest:
                tokens.push(Token(kind = TokenKind.DoubleRAngle, text = ">>"))
                byteIdx += 2

            ">=" rest:
                tokens.push(Token(kind = TokenKind.RAngleEq, text = ">="))
                byteIdx += 2

            ">" rest:
                tokens.push(Token(kind = TokenKind.RAngle, text = ">"))
                byteIdx += 1

            ########################################################################################
            # Literals

            other:
                panic("Invalid token at `byteIdx`")

# TODO: Handle nested comments.
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
