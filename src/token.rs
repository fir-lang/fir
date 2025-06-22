use smol_str::SmolStr;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub text: SmolStr,
}

impl Token {
    pub fn smol_str(&self) -> SmolStr {
        match self.kind {
            // Drop the '~' in tokens that merged with a prefix '~' to avoid LR(1) issues in the
            // parser.
            //
            // We don't drop the brackets as those tokens are generated in a later pass after
            // lexing, and text does not include the brackets.
            TokenKind::TildeUpperId
            | TokenKind::TildeUpperIdPath
            | TokenKind::TildeUpperIdLBracket
            | TokenKind::TildeUpperIdPathLBracket => SmolStr::new(&self.text[1..]),

            _ => self.text.clone(),
        }
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

    /// An identifier starting with a '~' followed by uppercase letter.
    TildeUpperId,

    /// `'~' UpperId '.' UpperId`, without spaces in between.
    TildeUpperIdPath,

    TildeUpperIdPathLBracket,

    TildeUpperIdLBracket,

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
    Export,
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
    Int,
    HexInt,
    BinInt,
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
