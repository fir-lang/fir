use crate::ast;
use crate::lexer::lex;
use crate::parser::LExprParser;
use crate::token::Token;

use std::rc::Rc;

use lexgen_util::Loc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StringPart {
    Str(String),
    Expr(ast::L<ast::Expr>),
}

// Lexer ensures any interpolation (the part between `$(` and `)`) have balanced parens. In
// addition, we don't handle string literals inside interpolations, so interpolations can't be
// nested.
pub fn parse_string_parts(module: &Rc<str>, s: &str) -> Vec<StringPart> {
    let mut parts: Vec<StringPart> = vec![];

    let mut escape = false;
    let mut chars = s.char_indices();
    let mut str_part_start: usize = 0;

    'outer: while let Some((byte_idx, char)) = chars.next() {
        if escape {
            escape = false;
            continue;
        }

        if char == '\\' {
            escape = true;
            continue;
        }

        if char == '$' {
            if let Some((lparen_idx, '(')) = chars.next() {
                parts.push(StringPart::Str(s[str_part_start..byte_idx].to_string()));

                let mut parens: u32 = 1;
                for (byte_idx, char) in chars.by_ref() {
                    if escape {
                        escape = false;
                        continue;
                    }

                    if char == '\\' {
                        escape = true;
                        continue;
                    }

                    if char == '(' {
                        parens += 1;
                        continue;
                    }

                    if char == ')' {
                        parens -= 1;
                        if parens == 0 {
                            // Lex and parse interpolation.
                            let interpolation = &s[lparen_idx + 1..byte_idx];
                            let tokens: Vec<(Loc, Token, Loc)> = lex(interpolation);
                            let parser = LExprParser::new();
                            let expr = parser.parse(module, tokens).unwrap();
                            parts.push(StringPart::Expr(expr));
                            str_part_start = byte_idx + 1;
                            continue 'outer;
                        }
                    }
                }
            }
        }
    }

    if str_part_start != s.len() {
        parts.push(StringPart::Str(s[str_part_start..s.len()].to_string()));
    }

    parts
}

#[test]
fn interpolation_parsing_1() {
    let s = r#"abc"#;
    let parts = parse_string_parts(&"test".into(), s);
    assert_eq!(parts, vec![StringPart::Str("abc".into())]);
}

#[test]
fn interpolation_parsing_2() {
    let s = r#"abc $(a)"#;
    let parts = parse_string_parts(&"test".into(), s);
    assert_eq!(parts.len(), 2);
    assert_eq!(parts[0], StringPart::Str("abc ".into()));
    assert!(matches!(parts[1], StringPart::Expr(_)));
}
