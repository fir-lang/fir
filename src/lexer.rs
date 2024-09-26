use crate::token::*;

use lexgen_util::Loc;
use smol_str::SmolStr;

#[derive(Debug, Default)]
struct LexerState {}

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
        "impl" = TokenKind::Impl,
        "import" = TokenKind::Import,
        "in" = TokenKind::In,
        "jump" = TokenKind::Jump,
        "let" = TokenKind::Let,
        "match" = TokenKind::Match,
        "prim" = TokenKind::Prim,
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
        "..=" = TokenKind::DotDotEq,
        "_" = TokenKind::Underscore,

        // Operators
        "=" = TokenKind::Eq,
        "==" = TokenKind::EqEq,
        "+=" = TokenKind::PlusEq,
        "-=" = TokenKind::MinusEq,
        "*=" = TokenKind::StarEq,
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

        $$ascii_uppercase ($$ascii_alphanumeric | '_')* = TokenKind::UpperId,
        ($$ascii_lowercase | '_') ($$ascii_alphanumeric | '_')* = TokenKind::LowerId,

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

        "'" (_ # '\'') "'" = TokenKind::Char,
    }


    rule String {
        "`" => |lexer| lexer.switch(LexerRule::Interpolation),

        '"' => |lexer| lexer.switch_and_return(LexerRule::Init, TokenKind::String),

        // Escaped interpolation start
        "\\`" => |lexer| lexer.continue_(),

        // Escaped double quote
        '\\' '"' => |lexer| lexer.continue_(),

        _ => |lexer| lexer.continue_(),
    }

    rule Interpolation {
        "\\`" => |lexer| lexer.continue_(),

        "`" => |lexer| lexer.switch(LexerRule::String),

        _ => |lexer| lexer.continue_(),
    }
}

pub fn lex(src: &str, module: &str) -> Vec<(Loc, Token, Loc)> {
    let lexer = Lexer::new(src);
    lexer
        .map(|t| {
            let (l, t, r) = t.unwrap_or_else(|err| {
                panic!(
                    "{}:{}:{}: {:?}",
                    module, err.location.line, err.location.col, err.kind
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
