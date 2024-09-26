use smol_str::SmolStr;

#[derive(Debug, Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub text: SmolStr,
}

impl Token {
    pub fn smol_str(&self) -> SmolStr {
        self.text.clone()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    /// An identifier starting with an uppercase letter.
    UpperId,

    /// An identifier starting with a lowercase letter.
    LowerId,

    // Keywords
    As,
    Elif,
    Else,
    Export,
    Fn,
    For,
    If,
    Impl,
    Import,
    In,
    Jump,
    Let,
    Match,
    Prim,
    Return,
    Self_,
    Trait,
    Type,
    Var,
    While,

    // Delimiters
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    SingleQuote,

    // Punctuation
    Colon,
    Comma,
    Dot,
    Backslash,
    Underscore,

    // Operators
    Amp,
    AmpAmp,
    DotDot,
    DotDotEq,
    Eq,
    EqEq,
    Exclamation,
    ExclamationEq,
    LAngle,
    DoubleLAngle,
    LAngleEq,
    Minus,
    MinusEq,
    Pipe,
    PipePipe,
    Plus,
    PlusEq,
    RAngle,
    DoubleRAngle,
    RAngleEq,
    Star,
    StarEq,

    // Literals
    String,
    Int(Option<IntKind>),
    HexInt(Option<IntKind>),
    BinInt(Option<IntKind>),
    Char,

    // Virtual tokens, used to handle layout. Generatd by the scanner.
    Indent,
    Dedent,
    Newline,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntKind {
    I8,
    U8,
    I32,
    U32,
}
