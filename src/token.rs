use smol_str::SmolStr;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub text: SmolStr,
}

impl Token {
    pub fn lparen() -> Token {
        Token {
            kind: TokenKind::LParen,
            text: "(".into(),
        }
    }

    pub fn rparen() -> Token {
        Token {
            kind: TokenKind::RParen,
            text: ")".into(),
        }
    }

    pub fn lbrace() -> Token {
        Token {
            kind: TokenKind::LBrace,
            text: "{".into(),
        }
    }

    pub fn rbrace() -> Token {
        Token {
            kind: TokenKind::RBrace,
            text: "}".into(),
        }
    }

    pub fn lbracket() -> Token {
        Token {
            kind: TokenKind::LBracket,
            text: "[".into(),
        }
    }

    pub fn rbracket() -> Token {
        Token {
            kind: TokenKind::RBracket,
            text: "]".into(),
        }
    }

    pub fn comma() -> Token {
        Token {
            kind: TokenKind::Comma,
            text: ",".into(),
        }
    }

    pub fn semicolon() -> Token {
        Token {
            kind: TokenKind::Semicolon,
            text: ";".into(),
        }
    }

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
    Semicolon,
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
    Slash,
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
