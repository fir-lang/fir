use crate::token::*;

use lexgen_util::Loc;
use smol_str::SmolStr;

#[derive(Debug, Default)]
struct LexerState {
    /// When lexing interpolations, this holds the number of open left parens we've seen without a
    /// closing pair. When this is zero and we see a closing paren, that ends the interpolation.
    ///
    /// Note: for now we don't allow strings in interpolations.
    open_parens: u32,
}

lexgen::lexer! {
    pub Lexer(LexerState) -> TokenKind;

    rule Init {

        // Skip whitespace
        [' ' '\n'],

        // Skip comments
        "#" (_ # '\n')* '\n',

        // Keywords
        "as" = TokenKind::As,
        "elif" = TokenKind::Elif,
        "else" = TokenKind::Else,
        "export" = TokenKind::Export,
        "fn" = TokenKind::Fn,
        "for" = TokenKind::For,
        "if" = TokenKind::If,
        "import" = TokenKind::Import,
        "in" = TokenKind::In,
        "jump" = TokenKind::Jump,
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
        "<=" = TokenKind::LAngleEq,
        ">" = TokenKind::RAngle,
        ">=" = TokenKind::RAngleEq,
        "!=" = TokenKind::ExclamationEq,

        $$ascii_uppercase ($$ascii_alphanumeric | '_')* = TokenKind::UpperId,
        $$ascii_lowercase ($$ascii_alphanumeric | '_')* = TokenKind::LowerId,

        // Literals
        '"' => |lexer| {
            lexer.switch(LexerRule::String)
        },

        ['0'-'9']+ = TokenKind::Int,
    }


    // Check nesting of `$(...)` parts. Parsing is done later.
    rule String {
        "$(" => |lexer| {
            lexer.state().open_parens = 0;
            lexer.switch(LexerRule::Interpolation)
        },

        '"' => |lexer| lexer.switch_and_return(LexerRule::Init, TokenKind::String),

        // Escaped interpolation start
        "\\$(" => |lexer| lexer.continue_(),

        // Escaped double quote
        '\\' '"' => |lexer| lexer.continue_(),

        _ => |lexer| lexer.continue_(),
    }

    rule Interpolation {
        '(' => |lexer| {
            lexer.state().open_parens += 1;
            lexer.continue_()
        },

        ')' => |lexer| {
            match lexer.state().open_parens {
                0 => lexer.switch(LexerRule::String),
                _ => {
                    lexer.state().open_parens -= 1;
                    lexer.continue_()
                }
            }
        },

        _ => |lexer| lexer.continue_(),
    }
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
                    text: SmolStr::new(&src[l.byte_idx..r.byte_idx]),
                },
                r,
            )
        })
        .collect()
}
