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
        '#' (_ # '|') (_ # '\n')* '\n',

        "#|" => |lexer| {
            lexer.switch(LexerRule::Comment)
        },

        // Keywords
        "as" = TokenKind::As,
        "break" = TokenKind::Break,
        "continue" = TokenKind::Continue,
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
        "jump" = TokenKind::Jump,
        "let" = TokenKind::Let,
        "loop" = TokenKind::Loop,
        "match" = TokenKind::Match,
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
        "..=" = TokenKind::DotDotEq,
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

        let upper_id = $$ascii_uppercase ($$ascii_alphanumeric | '_')*;
        '~' $upper_id = TokenKind::TildeUpperId,
        $upper_id = TokenKind::UpperId,
        ($$ascii_lowercase | '_') ($$ascii_alphanumeric | '_')* = TokenKind::LowerId,

        '\'' $$ascii_lowercase ($$ascii_alphanumeric | '_')+ = TokenKind::Label,

        // Literals
        '"' => |lexer| {
            lexer.switch(LexerRule::String)
        },

        // TODO: We should probably leave defaulting to the type checker.
        let int = ['0'-'9' '_']+;
        $int+ = TokenKind::Int(None),
        $int+ "i32" = TokenKind::Int(Some(IntKind::I32)),
        $int+ "u32" = TokenKind::Int(Some(IntKind::U32)),
        $int+ "i8" = TokenKind::Int(Some(IntKind::I8)),
        $int+ "u8" = TokenKind::Int(Some(IntKind::U8)),

        let hex_int = ['0'-'9' 'a'-'f' 'A'-'F' '_']+;
        "0x" $hex_int+ = TokenKind::HexInt(None),
        "0x" $hex_int+ "i32" = TokenKind::HexInt(Some(IntKind::I32)),
        "0x" $hex_int+ "u32" = TokenKind::HexInt(Some(IntKind::U32)),
        "0x" $hex_int+ "i8" = TokenKind::HexInt(Some(IntKind::I8)),
        "0x" $hex_int+ "u8" = TokenKind::HexInt(Some(IntKind::U8)),

        let bin_int = ['0' '1' '_']+;
        "0b" $bin_int+ = TokenKind::BinInt(None),
        "0b" $bin_int+ "i32" = TokenKind::BinInt(Some(IntKind::I32)),
        "0b" $bin_int+ "u32" = TokenKind::BinInt(Some(IntKind::U32)),
        "0b" $bin_int+ "i8" = TokenKind::BinInt(Some(IntKind::I8)),
        "0b" $bin_int+ "u8" = TokenKind::BinInt(Some(IntKind::U8)),

        "'" ((_ # '\'') | "\\'" | "\\n" | "\\t" | "\\r" | "\\\\") "'" = TokenKind::Char,
    }


    rule String {
        "`" => |lexer| lexer.switch(LexerRule::Interpolation),

        '"' => |lexer| lexer.switch_and_return(LexerRule::Init, TokenKind::String),

        // Escaped interpolation start
        "\\`" => |lexer| lexer.continue_(),

        // Escape characters
        '\\' ('"' | 'n' | 't' | 'r' | '\\') => |lexer| lexer.continue_(),

        _ => |lexer| lexer.continue_(),
    }

    rule Interpolation {
        "\\`" => |lexer| lexer.continue_(),

        "`" => |lexer| lexer.switch(LexerRule::String),

        _ => |lexer| lexer.continue_(),
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
