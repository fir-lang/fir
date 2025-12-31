use crate::token::*;

use lexgen_util::Loc;
use smol_str::SmolStr;

#[derive(Debug, Default)]
struct LexerState {
    stack: Vec<State>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum State {
    Init,
    Comment,
    String,
}

lexgen::lexer! {
    pub Lexer(LexerState) -> TokenKind;

    type Error = String;

    rule Init {
        // Skip whitespace
        [' ' '\n'],

        // Skip comments
        '#',
        '#' '\n',
        '#' (_ # ['|' '\n']) (_ # '\n')* '\n',

        "#|" => |lexer| {
            lexer.state().stack.push(State::Init);
            lexer.switch(LexerRule::Comment)
        },

        '`' =? |lexer| {
            match lexer.state().stack.pop() {
                Some(State::String) => {
                    lexer.switch_and_return(LexerRule::String, Ok(TokenKind::EndInterpolation))
                }
                _ => {
                    lexer.return_(Err("Backtick outside of a string interpolation".to_string()))
                }
            }
        },

        // Keywords
        "and" = TokenKind::And,
        "as" = TokenKind::As,
        "break" = TokenKind::Break,
        "continue" = TokenKind::Continue,
        "do" = TokenKind::Do,
        "elif" = TokenKind::Elif,
        "else" = TokenKind::Else,
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
        "return" = TokenKind::Return,
        "trait" = TokenKind::Trait,
        "type" = TokenKind::Type,
        "var" = TokenKind::Var,
        "while" = TokenKind::While,

        // Delimiters
        "\\(" = TokenKind::BackslashLParen,
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

        $upper_id ('.' $upper_id)* = TokenKind::UpperIdPath,

        '_'* $$ascii_lowercase ($$ascii_alphanumeric | '_')* = TokenKind::LowerId,

        '\'' $$ascii_lowercase ($$ascii_alphanumeric | '_')* = TokenKind::Label,

        $upper_id ".[" = TokenKind::UpperIdDotLBracket,

        // Literals
        '"' => |lexer| {
            lexer.state().stack.push(State::Init);
            lexer.switch_and_return(LexerRule::String, TokenKind::BeginStr)
        },

        let int = ['0'-'9'] ['0'-'9' '_']*;
        '-'? $int+ = TokenKind::Int,

        let hex_int = ['0'-'9' 'a'-'f' 'A'-'F' '_']+;
        '-'? "0x" $hex_int+ = TokenKind::HexInt,

        let bin_int = ['0' '1' '_']+;
        '-'? "0b" $bin_int+ = TokenKind::BinInt,

        "'" ((_ # '\'') | "\\'" | "\\n" | "\\t" | "\\r" | "\\\\") "'" = TokenKind::Char,
    }


    rule String {
        "`" => |lexer| {
            lexer.state().stack.push(State::String);
            lexer.switch_and_return(LexerRule::Init, TokenKind::BeginInterpolation)
        },

        '"' => |lexer| {
            let state = lexer.state().stack.pop();
            debug_assert_eq!(state, Some(State::Init));
            lexer.switch_and_return(LexerRule::Init, TokenKind::EndStr)
        },

        // Escaped interpolation start
        "\\`" => |lexer| lexer.continue_(),

        // Escape characters
        '\\' ('"' | 'n' | 't' | 'r' | '\\') => |lexer| lexer.continue_(),

        // "Continuation escape": backslash followed by newline ignores the newline and following
        // whitespace.
        '\\' '\n' => |lexer| {
            lexer.switch(LexerRule::StringSkipWhitespace)
        },

        _ => |lexer| lexer.continue_(),
    }

    rule StringSkipWhitespace {
        ' ' | '\t' | '\n' | '\r' => |lexer| lexer.continue_(),

        '"' => |lexer| lexer.switch_and_return(LexerRule::Init, TokenKind::EndStr),

        // TODO: This will consume backslash, backtick before switching.
        _ => |lexer| lexer.switch(LexerRule::String),
    }

    rule Comment {
        "#|" =>
            |lexer| {
                lexer.state().stack.push(State::Comment);
                lexer.continue_()
            },

        "|#" =>
            |lexer| {
                match lexer.state().stack.pop().unwrap() {
                    State::Comment => {
                        lexer.continue_()
                    }
                    State::Init => {
                        lexer.reset_match();
                        lexer.switch(LexerRule::Init)
                    }
                    State::String => {
                        panic!() // bug in state handling
                    }
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
