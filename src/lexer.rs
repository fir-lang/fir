use crate::token::*;

use lexgen_util::Loc;
use smol_str::SmolStr;

#[derive(Debug, Default)]
struct LexerState {
    comment_depth: u32,
}

lexgen::lexer! {
    pub Lexer(LexerState) -> TokenKind;

    rule Init {

        // Skip whitespace
        [' ' '\n'],

        // Skip comments
        '#',
        '#' '\n',
        '#' (_ # ('|' | '[')) (_ # '\n')* '\n',

        "#|" => |lexer| {
            lexer.switch(LexerRule::Comment)
        },

        "#[" = TokenKind::HashLBracket,

        // Keywords
        "and" = TokenKind::And,
        "as" = TokenKind::As,
        "break" = TokenKind::Break,
        "continue" = TokenKind::Continue,
        "do" = TokenKind::Do,
        "elif" = TokenKind::Elif,
        "else" = TokenKind::Else,
        "export" = TokenKind::Export,
        "fn" = TokenKind::Fn,
        "Fn" = TokenKind::UpperFn,
        "for" = TokenKind::For,
        "if" = TokenKind::If,
        "impl" = TokenKind::Impl,
        "import" = TokenKind::Import,
        "in" = TokenKind::In,
        "is" = TokenKind::Is,
        "jump" = TokenKind::Jump,
        "let" = TokenKind::Let,
        "loop" = TokenKind::Loop,
        "match" = TokenKind::Match,
        "not" = TokenKind::Not,
        "or" = TokenKind::Or,
        "prim" = TokenKind::Prim,
        "return" = TokenKind::Return, // maybe shorten as "ret"?
        "trait" = TokenKind::Trait,
        "type" = TokenKind::Type,
        "var" = TokenKind::Var,
        "while" = TokenKind::While,

        // Delimiters
        "(" = TokenKind::LParen,
        "row(" = TokenKind::LParenRow,
        ")" = TokenKind::RParen,
        "[" = TokenKind::LBracket,
        "row[" = TokenKind::LBracketRow,
        "]" = TokenKind::RBracket,
        "{" = TokenKind::LBrace,
        "}" = TokenKind::RBrace,
        "'" = TokenKind::SingleQuote,

        // Punctuation
        "." = TokenKind::Dot,
        "," = TokenKind::Comma,
        ":" = TokenKind::Colon,
        ";" = TokenKind::Semicolon,
        "\\" = TokenKind::Backslash,
        ".." = TokenKind::DotDot,
        "_" = TokenKind::Underscore,

        // Operators
        "=" = TokenKind::Eq,
        "==" = TokenKind::EqEq,
        "+=" = TokenKind::PlusEq,
        "-=" = TokenKind::MinusEq,
        "*=" = TokenKind::StarEq,
        "^=" = TokenKind::CaretEq,
        "+" = TokenKind::Plus,
        "-" = TokenKind::Minus,
        "*" = TokenKind::Star,
        "!" = TokenKind::Exclamation,
        "&" = TokenKind::Amp,
        "&&" = TokenKind::AmpAmp,
        "|" = TokenKind::Pipe,
        "||" = TokenKind::PipePipe,
        "<" = TokenKind::LAngle,
        "<<" = TokenKind::DoubleLAngle,
        "<=" = TokenKind::LAngleEq,
        ">" = TokenKind::RAngle,
        ">>" = TokenKind::DoubleRAngle,
        ">=" = TokenKind::RAngleEq,
        "!=" = TokenKind::ExclamationEq,
        "/" = TokenKind::Slash,
        "~" = TokenKind::Tilde,
        "%" = TokenKind::Percent,
        "^" = TokenKind::Caret,

        let upper_id = '_'* $$ascii_uppercase ($$ascii_alphanumeric | '_')*;

        $upper_id = TokenKind::UpperId,
        '~' $upper_id = TokenKind::TildeUpperId,

        $upper_id '.' $upper_id = TokenKind::UpperIdPath,
        '~' $upper_id '.' $upper_id = TokenKind::TildeUpperIdPath,

        '_'* $$ascii_lowercase ($$ascii_alphanumeric | '_')* = TokenKind::LowerId,

        '\'' $$ascii_lowercase ($$ascii_alphanumeric | '_')* = TokenKind::Label,

        $upper_id ".[" = TokenKind::UpperIdDotLBracket,

        // Literals
        '"' => |lexer| {
            lexer.switch(LexerRule::String)
        },

        let int = ['0'-'9'] ['0'-'9' '_']*;
        $int+ = TokenKind::Int,

        let hex_int = ['0'-'9' 'a'-'f' 'A'-'F' '_']+;
        "0x" $hex_int+ = TokenKind::HexInt,

        let bin_int = ['0' '1' '_']+;
        "0b" $bin_int+ = TokenKind::BinInt,

        "'" ((_ # '\'') | "\\'" | "\\n" | "\\t" | "\\r" | "\\\\") "'" = TokenKind::Char,
    }


    rule String {
        "`" => |lexer| lexer.switch(LexerRule::Interpolation),

        '"' => |lexer| lexer.switch_and_return(LexerRule::Init, TokenKind::Str),

        // Escaped interpolation start
        "\\`" => |lexer| lexer.continue_(),

        // Escape characters
        '\\' ('"' | 'n' | 't' | 'r' | '\\') => |lexer| lexer.continue_(),

        // "Continuation escape": backslash followed by newline ignores the newline and following
        // whitespace.
        '\\' '\n' => |lexer| lexer.switch(LexerRule::StringSkipWhitespace),

        _ => |lexer| lexer.continue_(),
    }

    rule Interpolation {
        "\\`" => |lexer| lexer.continue_(),

        "`" => |lexer| lexer.switch(LexerRule::String),

        _ => |lexer| lexer.continue_(),
    }

    rule StringSkipWhitespace {
        ' ' | '\t' | '\n' | '\r' => |lexer| lexer.continue_(),
        '"' => |lexer| lexer.switch_and_return(LexerRule::Init, TokenKind::Str),
        _ => |lexer| lexer.switch(LexerRule::String),
    }

    rule Comment {
        "#|" =>
            |lexer| {
                lexer.state().comment_depth += 1;
                lexer.continue_()
            },

        "|#" =>
            |lexer| {
                let depth = &mut lexer.state().comment_depth;
                if *depth == 0 {
                    lexer.switch(LexerRule::Init)
                } else {
                    *depth -= 1;
                    lexer.continue_()
                }
            },

        _,
    },
}

pub fn lex(src: &str, module: &str) -> Vec<(Loc, Token, Loc)> {
    let lexer = Lexer::new(src);
    lexer
        .map(|t| {
            let (l, t, r) = t.unwrap_or_else(|err| {
                panic!(
                    "{}:{}:{}: {:?}",
                    module,
                    err.location.line + 1,
                    err.location.col + 1,
                    err.kind
                )
            });
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

#[test]
fn lex_ids() {
    let input = "a _a __a __a__a_ B _B __B __B__B_";
    let tokens: Vec<Token> = lex(input, "test").into_iter().map(|(_, t, _)| t).collect();
    assert_eq!(
        tokens,
        vec![
            Token {
                kind: TokenKind::LowerId,
                text: "a".into(),
            },
            Token {
                kind: TokenKind::LowerId,
                text: "_a".into(),
            },
            Token {
                kind: TokenKind::LowerId,
                text: "__a".into(),
            },
            Token {
                kind: TokenKind::LowerId,
                text: "__a__a_".into(),
            },
            Token {
                kind: TokenKind::UpperId,
                text: "B".into(),
            },
            Token {
                kind: TokenKind::UpperId,
                text: "_B".into(),
            },
            Token {
                kind: TokenKind::UpperId,
                text: "__B".into(),
            },
            Token {
                kind: TokenKind::UpperId,
                text: "__B__B_".into(),
            }
        ]
    );
}

#[test]
fn lex_underscores() {
    let input = "__";
    let tokens: Vec<Token> = lex(input, "test").into_iter().map(|(_, t, _)| t).collect();
    assert_eq!(
        tokens,
        vec![
            Token {
                kind: TokenKind::Underscore,
                text: "_".into(),
            },
            Token {
                kind: TokenKind::Underscore,
                text: "_".into(),
            }
        ]
    );
}
