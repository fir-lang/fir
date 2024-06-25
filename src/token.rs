use smol_str::SmolStr;

#[derive(Debug, Clone, Copy)]
pub struct Token<'a> {
    pub kind: TokenKind,
    pub text: &'a str,
}

impl<'a> Token<'a> {
    pub fn smol_str(&self) -> SmolStr {
        SmolStr::new(self.text)
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
    Import,
    In,
    Jump,
    Let,
    Match,
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
    Eq,
    EqEq,
    ExclamationEq,
    PlusEq,
    MinusEq,
    DotDot,
    Plus,
    Minus,
    Star,
    Exclamation,
    AmpAmp,
    PipePipe,
    LAngle,
    LAngleEq,
    RAngle,
    RAngleEq,

    // Literals
    String,
    Int,

    // Virtual tokens, used to handle layout. Generatd by the scanner.
    Indent,
    Dedent,
    Newline,
}
