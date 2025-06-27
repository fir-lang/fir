use crate::ast;
use crate::lexer::lex;
use crate::parser::LExprParser;
use crate::token::Token;

use std::rc::Rc;

use lexgen_util::Loc;
use smol_str::SmolStr;

#[derive(Debug, Clone)]
pub enum StringPart {
    Str(String),
    Expr(ast::L<ast::Expr>),
}

// Lexer ensures any interpolation (the part between `$(` and `)`) have balanced parens. In
// addition, we don't handle string literals inside interpolations, so interpolations can't be
// nested.
pub fn parse_string_parts(module: &Rc<str>, s: &str, mut loc: Loc) -> Vec<StringPart> {
    let mut parts: Vec<StringPart> = vec![];

    let mut escape = false;
    let mut chars = s.char_indices().peekable();
    let mut str_part_start: usize = 0;

    'outer: while let Some((byte_idx, char)) = chars.next() {
        if char == '\n' {
            loc.line += 1;
            loc.col = 0;
        } else {
            loc.col += 1;
        }

        loc.byte_idx += char.len_utf8();

        if escape {
            escape = false;
            continue;
        }

        if char == '\\' {
            if let Some((_, '\n')) = chars.peek() {
                while let Some((_, ' ' | '\t' | '\n' | '\r')) = chars.peek() {
                    chars.next();
                }
                escape = false;
                continue;
            }
            escape = true;
            continue;
        }

        if char == '`' {
            let start_byte = byte_idx;
            let start_loc = Loc {
                line: loc.line,
                col: loc.col,
                byte_idx: loc.byte_idx,
            };

            parts.push(StringPart::Str(copy_update_escapes(
                &s[str_part_start..byte_idx],
            )));

            for (byte_idx, char) in chars.by_ref() {
                if char == '\n' {
                    loc.line += 1;
                    loc.col = 0;
                } else {
                    loc.col += 1;
                }

                loc.byte_idx += char.len_utf8();

                if escape {
                    escape = false;
                    continue;
                }

                if char == '\\' {
                    escape = true;
                    continue;
                }

                if char == '`' {
                    // Lex and parse interpolation.
                    let interpolation = &s[start_byte + 1..byte_idx];
                    let mut tokens: Vec<(Loc, Token, Loc)> = lex(interpolation, module);
                    for (l, _, r) in &mut tokens {
                        *l = update_loc(l, &start_loc);
                        *r = update_loc(r, &start_loc);
                    }
                    let parser = LExprParser::new();
                    let expr = match parser.parse(module, tokens) {
                        Ok(expr) => expr,
                        Err(err) => crate::report_parse_error(&SmolStr::new(module), err),
                    };
                    parts.push(StringPart::Expr(expr));
                    str_part_start = byte_idx + 1;
                    continue 'outer;
                }
            }
        }
    }

    if str_part_start != s.len() {
        parts.push(StringPart::Str(copy_update_escapes(
            &s[str_part_start..s.len()],
        )));
    }

    parts
}

fn update_loc(err_loc: &Loc, start_loc: &Loc) -> Loc {
    let byte_idx = err_loc.byte_idx + start_loc.byte_idx;
    if err_loc.line == 0 {
        Loc {
            line: start_loc.line,
            col: start_loc.col + err_loc.col,
            byte_idx,
        }
    } else {
        Loc {
            line: start_loc.line + err_loc.line,
            col: err_loc.col,
            byte_idx,
        }
    }
}

/// Copy the tokenized string, converting escape sequences to characters.
pub(crate) fn copy_update_escapes(s: &str) -> String {
    let mut ret = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();

    while let Some(char) = chars.next() {
        if char == '\\' {
            // Escape sequences are recognized by the lexer, so we know '\\' is followed by one of
            // the characters below.
            match chars.next().unwrap() {
                '\\' => ret.push('\\'),
                'n' => ret.push('\n'),
                't' => ret.push('\t'),
                'r' => ret.push('\r'),
                '"' => ret.push('"'),
                '`' => ret.push('`'),
                '\n' => {
                    while let Some(next) = chars.peek().copied() {
                        match next {
                            ' ' | '\t' | '\n' | '\r' => {
                                chars.next();
                            }
                            _ => break,
                        }
                    }
                }
                other => panic!("Weird escape character: {other:?}"),
            }
        } else {
            ret.push(char);
        }
    }

    ret
}

#[cfg(test)]
impl StringPart {
    fn as_str(&self) -> &str {
        match self {
            StringPart::Str(str) => str,
            StringPart::Expr(_) => panic!(),
        }
    }

    fn as_expr(&self) -> &ast::L<ast::Expr> {
        match self {
            StringPart::Str(_) => panic!(),
            StringPart::Expr(expr) => expr,
        }
    }
}

#[test]
fn interpolation_parsing_1() {
    let s = r#"abc"#;
    let parts = parse_string_parts(&"test".into(), s, Loc::default());
    assert_eq!(parts.len(), 1);
    assert_eq!(parts[0].as_str(), "abc");
}

#[test]
fn interpolation_parsing_2() {
    let s = r#"abc `a`"#;
    let parts = parse_string_parts(&"test".into(), s, Loc::default());
    assert_eq!(parts.len(), 2);
    assert_eq!(parts[0].as_str(), "abc ");
    parts[1].as_expr();
}
