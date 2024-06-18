use crate::token::*;

use lexgen_util::Loc;

lexgen::lexer! {
    pub Lexer -> TokenKind;

    // Skip whitespace
    [' ' '\n'],

    // Skip comments
    "--" (_ # '\n')* '\n',

    // Keywords
    "elif" = TokenKind::Elif,
    "else" = TokenKind::Else,
    "fn" = TokenKind::Fn,
    "for" = TokenKind::For,
    "if" = TokenKind::If,
    "in" = TokenKind::In,
    "let" = TokenKind::Let,
    "match" = TokenKind::Match,
    "return" = TokenKind::Return, // maybe shorten as "ret"?
    "self" = TokenKind::Self_,
    "trait" = TokenKind::Trait,
    "type" = TokenKind::Type,
    "var" = TokenKind::Var,
    "while" = TokenKind::While,

    // Delimiters
    "(" = TokenKind::LParen,
    ")" = TokenKind::RParen,
    "[" = TokenKind::LBracket,
    "]" = TokenKind::RBracket,
    "{" = TokenKind::LBrace,
    "}" = TokenKind::RBrace,
    "'" = TokenKind::SingleQuote,
    "\"" = TokenKind::DoubleQuote,

    // Punctuation
    "." = TokenKind::Dot,
    "," = TokenKind::Comma,
    ":" = TokenKind::Colon,
    "\\" = TokenKind::Backslash,
    ".." = TokenKind::DotDot,
    "_" = TokenKind::Underscore,

    // Operators
    "=" = TokenKind::Eq,
    "==" = TokenKind::EqEq,
    "+=" = TokenKind::PlusEq,
    "-=" = TokenKind::MinusEq,
    "+" = TokenKind::Plus,
    "-" = TokenKind::Minus,
    "*" = TokenKind::Star,
    "!" = TokenKind::Exclamation,
    "&&" = TokenKind::AmpAmp,
    "||" = TokenKind::PipePipe,
    "<" = TokenKind::LAngle,
    ">" = TokenKind::RAngle,
    "!=" = TokenKind::ExclamationEq,

    $$ascii_uppercase ($$ascii_alphanumeric | '_')* = TokenKind::UpperId,
    $$ascii_lowercase ($$ascii_alphanumeric | '_')* = TokenKind::LowerId,

    // Literals
    '"' ((_ # '"') | "\\\"")* '"' = TokenKind::String,
    ['0'-'9']+ = TokenKind::Int,
}

pub fn lex(src: &str) -> Vec<(Loc, Token, Loc)> {
    let lexer = Lexer::new(src);
    lexer
        .map(|t| {
            let (l, t, r) = t.unwrap();
            (
                l,
                Token {
                    kind: t,
                    text: &src[l.byte_idx..r.byte_idx],
                },
                r,
            )
        })
        .collect()
}
