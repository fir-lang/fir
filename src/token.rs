use smol_str::SmolStr;

#[derive(Debug, Clone, PartialEq, Eq)]
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

    /// `UpperId '.' UpperId`, without spaces in between.
    UpperIdPath,

    /// `UpperId '.' UpperId`, follwed by a '['.
    UpperIdPathLBracket,

    /// An identifier starting with an uppercase letter, followed by a '['.
    UpperIdLBracket,

    /// An identifier starting with an uppercase letter, followed by a '.['.
    ///
    /// This starts an iterator syntax.
    UpperIdDotLBracket,

    /// An identifier starting with a lowercase letter.
    LowerId,

    /// A label is a lowercase id that starts with a single quote.
    Label,

    // Keywords
    And,
    As,
    Break,
    Continue,
    Do,
    Elif,
    Else,
    Fn,
    For,
    If,
    Impl,
    Import,
    In,
    Is,
    Jump,
    Let,
    Loop,
    Match,
    Not,
    Or,
    Prim,
    Return,
    Trait,
    Type,
    UpperFn,
    Value,
    Var,
    While,

    // Delimiters
    LParen,
    LParenRow,
    RParen,
    LBracket,
    LBracketRow,
    RBracket,
    LBrace,
    RBrace,
    SingleQuote,
    BackslashLParen,

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
    Int,
    Char,

    // Virtual tokens, used to handle layout. Generatd by the scanner.
    Indent,
    Dedent,
    Newline,

    // Strings
    BeginStr,
    EndStr,
    BeginInterpolation,
    EndInterpolation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntKind {
    I8(i8),
    U8(u8),
    I32(i32),
    U32(u32),
    I64(i64),
    U64(u64),
}
