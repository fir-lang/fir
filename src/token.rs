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
    TildeUpperId,

    /// An identifier starting with a lowercase letter.
    LowerId,

    /// A label is a lowercase id that starts with a single quote.
    Label,

    // Keywords
    As,
    Break,
    Continue,
    Elif,
    Else,
    Export,
    Fn,
    UpperFn,
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
    Trait,
    Type,
    Var,
    While,
    Loop,

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
    Semicolon,
    Comma,
    Dot,
    Backslash,
    Underscore,

    // Operators
    Amp,
    AmpAmp,
    Caret,
    CaretEq,
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
    Percent,
    Pipe,
    PipePipe,
    Plus,
    PlusEq,
    RAngle,
    DoubleRAngle,
    RAngleEq,
    Slash,
    Star,
    StarEq,
    Tilde,

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
