use crate::token::{Token, TokenKind};

use std::cmp::Ordering;
use std::iter::Peekable;

use lexgen_util::Loc;

/// Entry point for scanning. Starts with an indented code as top-level code are indented.
pub fn scan<I>(token_iter: I, module: &str) -> Vec<(Loc, Token, Loc)>
where
    I: Iterator<Item = (Loc, Token, Loc)>,
{
    let mut new_tokens: Vec<(Loc, Token, Loc)> = vec![];
    let mut tokens = token_iter.peekable();
    let start_loc = match tokens.peek() {
        Some((l, _, _)) => *l,
        None => return vec![],
    };
    scan_indented(&mut tokens, module, &mut new_tokens, start_loc);
    assert_eq!(tokens.next(), None, "module = {module}");
    new_tokens
}

/// Scan an indented block. Indented blocks start with:
///
/// - `:` followed by a token in a new line
/// - `{`
///
/// In both cases, `start_loc` should be the location of the token of the first token of the block.
/// I.e. not the location of `{` but the token after it.
///
/// This function does not consume the token terminating the block, i.e. `}` or the dedented token.
pub fn scan_indented<I>(
    tokens: &mut Peekable<I>,
    module: &str,
    new_tokens: &mut Vec<(Loc, Token, Loc)>,
    start_loc: Loc,
) where
    I: Iterator<Item = (Loc, Token, Loc)>,
{
    let mut generate_newline = true;

    let mut last_loc = start_loc;

    while let Some((l, t, _)) = tokens.peek() {
        if matches!(
            t.kind,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace | TokenKind::Comma
        ) {
            if generate_newline {
                new_tokens.push(newline(last_loc));
            }
            return;
        }

        if l.line != last_loc.line {
            match l.col.cmp(&start_loc.col) {
                Ordering::Greater => {}

                Ordering::Equal => {
                    if generate_newline {
                        new_tokens.push(newline(last_loc));
                    }
                }

                Ordering::Less => {
                    if generate_newline {
                        new_tokens.push(newline(last_loc));
                    }
                    return;
                }
            }
        }

        generate_newline = true;

        let (l, t, r) = tokens.next().unwrap(); // increment the iterator

        last_loc = r;

        let kind = t.kind;
        new_tokens.push((l, t, r));

        match kind {
            TokenKind::LParen | TokenKind::LParenRow | TokenKind::BackslashLParen => {
                scan_non_indented(tokens, module, new_tokens, NonIndentedDelimKind::Paren);
                last_loc = new_tokens.last().unwrap().2;
            }

            TokenKind::LBracket | TokenKind::LBracketRow | TokenKind::UpperIdDotLBracket => {
                scan_non_indented(tokens, module, new_tokens, NonIndentedDelimKind::Bracket);
                last_loc = new_tokens.last().unwrap().2;
            }

            TokenKind::LBrace => match tokens.peek() {
                Some(next) => {
                    let start_loc = next.0;
                    scan_indented(tokens, module, new_tokens, start_loc);
                    match tokens.next() {
                        Some((
                            l,
                            t @ Token {
                                kind: TokenKind::RBrace,
                                ..
                            },
                            r,
                        )) => {
                            new_tokens.push((l, t, r));
                        }
                        _ => panic!(
                            "{}:{}:{}: unterminated '{{' block",
                            module,
                            l.line + 1,
                            l.col + 1
                        ),
                    }
                    last_loc = new_tokens.last().unwrap().2;
                    generate_newline = false;
                }
                None => {
                    return;
                }
            },

            TokenKind::Colon => {
                // Start an indented block if the next token is on a new line.
                if let Some((l, _, _)) = tokens.peek()
                    && l.line != last_loc.line
                {
                    let l = *l;

                    // `scanIndented` will generate indentation tokens for the indented block.
                    // Generate the wrapping `NEWLINE` + `INDENT` and `DEDENT` here.
                    new_tokens.push(newline(last_loc));
                    new_tokens.push(indent(Loc {
                        line: last_loc.line + 1,
                        col: 0,
                        byte_idx: last_loc.byte_idx + 1,
                    }));

                    scan_indented(tokens, module, new_tokens, l);

                    // Q: Should `scan_indented` return the last token location?
                    last_loc = new_tokens.last().unwrap().2;

                    // Don't generate `NEWLINE` after a recursive call: the block will end with a
                    // `NEWLINE` when it's ends with a non-block, or or it'll end with a `DEDENT`
                    // when it ends with a block. In both cases we don't want a `NEWLINE`.
                    generate_newline = false;

                    new_tokens.push(dedent(last_loc));
                }
            }

            _ => {}
        }
    }

    if generate_newline {
        new_tokens.push(newline(last_loc));
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NonIndentedDelimKind {
    Paren,
    Bracket,
}

/// Scan a non-indented block: `(...)` or `[...]`.
///
/// Consumes the terminating `)` or `]`.
pub fn scan_non_indented<I>(
    tokens: &mut Peekable<I>,
    module: &str,
    new_tokens: &mut Vec<(Loc, Token, Loc)>,
    delim_kind: NonIndentedDelimKind,
) where
    I: Iterator<Item = (Loc, Token, Loc)>,
{
    while let Some((l, t, r)) = tokens.next() {
        let t_kind = t.kind;
        new_tokens.push((l, t, r));

        match t_kind {
            TokenKind::RParen => match delim_kind {
                NonIndentedDelimKind::Paren => {
                    // println!("Ending non-indented block at {}:{}", l.line + 1, l.col + 1);
                    return;
                }
                NonIndentedDelimKind::Bracket => {
                    panic!(
                        "{}:{}:{}: ')' without matching '('",
                        module,
                        l.line + 1,
                        l.col + 1
                    );
                }
            },

            TokenKind::RBracket => match delim_kind {
                NonIndentedDelimKind::Bracket => {
                    // println!("Ending non-indented block at {}:{}", l.line + 1, l.col + 1);
                    return;
                }
                NonIndentedDelimKind::Paren => {
                    panic!(
                        "{}:{}:{}: ']' without matching '['",
                        module,
                        l.line + 1,
                        l.col + 1
                    );
                }
            },

            TokenKind::LParen | TokenKind::LParenRow | TokenKind::BackslashLParen => {
                scan_non_indented(tokens, module, new_tokens, NonIndentedDelimKind::Paren);
            }

            TokenKind::LBracket | TokenKind::LBracketRow | TokenKind::UpperIdDotLBracket => {
                scan_non_indented(tokens, module, new_tokens, NonIndentedDelimKind::Bracket);
            }

            TokenKind::LBrace => {
                let start_loc = tokens.peek().unwrap().0;
                scan_indented(tokens, module, new_tokens, start_loc);
                match tokens.next() {
                    Some((
                        l,
                        t @ Token {
                            kind: TokenKind::RBrace,
                            ..
                        },
                        r,
                    )) => {
                        new_tokens.push((l, t, r));
                    }
                    _ => panic!(
                        "{}:{}:{}: unterminated '{{' block",
                        module,
                        l.line + 1,
                        l.col + 1
                    ),
                }
            }

            TokenKind::RBrace => {
                panic!(
                    "{}:{}:{}: '}}' without matching '{{'",
                    module,
                    l.line + 1,
                    l.col + 1
                );
            }

            TokenKind::Colon => {
                // Start an indented block if the next token is on a new line.
                if let Some((l_, _, _)) = tokens.peek().cloned()
                    && l_.line != l.line
                {
                    // `scanIndented` will generate indentation tokens for the indented block.
                    // Generate the wrapping `NEWLINE` + `INDENT` and `DEDENT` here.
                    new_tokens.push(newline(r));
                    new_tokens.push(indent(Loc {
                        line: l.line + 1,
                        col: 0,
                        byte_idx: l.byte_idx + 1,
                    }));

                    scan_indented(tokens, module, new_tokens, l_);

                    // `scanIndented` will stop at a ',', ')', or ']'. Generate `DEDENT` before the
                    // next token.
                    let last_token = new_tokens.last().unwrap();
                    new_tokens.push(dedent(Loc {
                        line: last_token.2.line,
                        col: last_token.2.col,
                        byte_idx: last_token.2.byte_idx,
                    }));
                }
            }

            _ => {}
        }
    }
}

fn newline(loc: Loc) -> (Loc, Token, Loc) {
    (
        loc,
        Token {
            kind: TokenKind::Newline,
            text: "".into(),
        },
        loc, // TODO: This is not right, but we don't seem to be using it
    )
}

fn indent(loc: Loc) -> (Loc, Token, Loc) {
    (
        loc,
        Token {
            kind: TokenKind::Indent,
            text: "".into(),
        },
        loc,
    )
}

fn dedent(loc: Loc) -> (Loc, Token, Loc) {
    (
        loc,
        Token {
            kind: TokenKind::Dedent,
            text: "".into(),
        },
        loc,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use TokenKind::*;

    use indoc::indoc;

    fn scan_wo_locs(input: &str) -> Vec<TokenKind> {
        scan(crate::lexer::lex(input, "test").into_iter(), "test")
            .into_iter()
            .map(|(_, t, _)| t.kind)
            .collect()
    }

    #[test]
    fn indent1() {
        let input = indoc! {"
            a
                b
                c
            d
        "};
        let toks = scan_wo_locs(input);
        #[rustfmt::skip]
        assert_eq!(
            toks,
            vec![
                LowerId, // a
                LowerId, // b
                LowerId, // c
                Newline,
                LowerId, // d
                Newline,
            ]
        );
    }

    #[test]
    fn dedent_multiple() {
        let input = indoc! {"
            a:
                b:
                    c
            d
        "};
        let toks = scan_wo_locs(input);
        #[rustfmt::skip]
        assert_eq!(
            toks,
            vec![
                LowerId, // a
                Colon,
                Newline,
                Indent,
                LowerId, // b
                Colon,
                Newline,
                Indent,
                LowerId, // c
                Newline,
                Dedent,
                Dedent,
                LowerId, // d
                Newline,
            ]
        );
    }

    #[test]
    fn dedent_eof() {
        // At the end of the input, we should terminate the open blocks.
        let input = indoc! {"
            a:
                b:
                    c
        "};
        let toks = scan_wo_locs(input);
        #[rustfmt::skip]
        assert_eq!(
            toks,
            vec![
                LowerId, // a
                Colon,
                Newline,
                Indent,
                LowerId, // b
                Colon,
                Newline,
                Indent,
                LowerId, // c
                Newline,
                Dedent,
                Dedent,
            ]
        );
    }

    #[test]
    fn line_joining_in_parens() {
        // At the end of the input, we should terminate the open blocks.
        let input = indoc! {"
            if True:
                test(test(
                            a,
                        b,
            c),
            x, y)
            z
        "};
        let toks = scan_wo_locs(input);
        #[rustfmt::skip]
        assert_eq!(
            toks,
            vec![
                If,
                UpperId,
                Colon,
                Newline,
                Indent,
                LowerId,
                LParen,
                    LowerId,
                    LParen,
                        LowerId,
                        Comma,
                        LowerId,
                        Comma,
                        LowerId,
                    RParen,
                    Comma,
                    LowerId,
                    Comma,
                    LowerId,
                    RParen,
                Newline,
                Dedent,
                LowerId,
                Newline,
            ]
        );
    }

    #[test]
    fn braces() {
        // At the end of the input, we should terminate the open blocks.
        let input = indoc! {"
            fn() {
                a
                b
            }
        "};
        let toks = scan_wo_locs(input);
        #[rustfmt::skip]
        assert_eq!(
            toks,
            vec![
                Fn,
                LParen,
                RParen,
                LBrace,
                    LowerId, // a
                    Newline,
                    LowerId, // b
                    Newline,
                RBrace,
            ]
        );
    }

    #[test]
    fn layout_after_comments() {
        // At the end of the input, we should terminate the open blocks.
        let input = indoc! {"
            symbolNonRec:
                a  # foo
                b  # bar
        "};
        let toks = scan_wo_locs(input);
        #[rustfmt::skip]
        assert_eq!(
            toks,
            vec![
                LowerId,
                Colon,
                Newline,
                Indent,
                    LowerId, // a
                    Newline,
                    LowerId, // b
                    Newline,
                Dedent,
            ]
        );
    }

    #[test]
    fn newline_token_location_1() {
        use smol_str::SmolStr;
        let input = "a\nb";
        let toks: Vec<(Loc, Token, Loc)> =
            scan(crate::lexer::lex(input, "test").into_iter(), "test");
        #[rustfmt::skip]
        assert_eq!(
            toks,
            [
                (
                    Loc { line: 0, col: 0, byte_idx: 0 },
                    Token { kind: LowerId, text: SmolStr::new("a") },
                    Loc { line: 0, col: 1, byte_idx: 1 }
                ),
                (
                    Loc { line: 0, col: 1, byte_idx: 1 },
                    Token { kind: Newline, text: SmolStr::new("") },
                    Loc { line: 0, col: 1, byte_idx: 1 }
                ),
                (
                    Loc { line: 1, col: 0, byte_idx: 2 },
                    Token { kind: LowerId, text: SmolStr::new("b") },
                    Loc { line: 1, col: 1, byte_idx: 3 }
                ),
                (
                    Loc { line: 1, col: 1, byte_idx: 3 },
                    Token { kind: Newline, text: SmolStr::new("") },
                    Loc { line: 1, col: 1, byte_idx: 3 }
                )
            ],
        );
    }

    #[test]
    fn newline_token_location_2() {
        use smol_str::SmolStr;
        let input = "a:\n    b";
        let toks: Vec<(Loc, Token, Loc)> =
            scan(crate::lexer::lex(input, "test").into_iter(), "test");
        #[rustfmt::skip]
        assert_eq!(
            toks,
            [
                (
                    Loc { line: 0, col: 0, byte_idx: 0 },
                    Token { kind: LowerId, text: SmolStr::new("a") },
                    Loc { line: 0, col: 1, byte_idx: 1 }
                ),
                (
                    Loc { line: 0, col: 1, byte_idx: 1 },
                    Token { kind: Colon, text: SmolStr::new(":") },
                    Loc { line: 0, col: 2, byte_idx: 2 }
                ),
                (
                    Loc { line: 0, col: 2, byte_idx: 2 },
                    Token { kind: Newline, text: SmolStr::new("") },
                    Loc { line: 0, col: 2, byte_idx: 2 }
                ),
                (
                    Loc { line: 1, col: 0, byte_idx: 3 },
                    Token { kind: Indent, text: SmolStr::new("") },
                    Loc { line: 1, col: 0, byte_idx: 3 }
                ),
                (
                    Loc { line: 1, col: 4, byte_idx: 7 },
                    Token { kind: LowerId, text: SmolStr::new("b") },
                    Loc { line: 1, col: 5, byte_idx: 8 }
                ),
                (
                    Loc { line: 1, col: 5, byte_idx: 8 },
                    Token { kind: Newline, text: SmolStr::new("") },
                    Loc { line: 1, col: 5, byte_idx: 8 }
                ),
                (
                    Loc { line: 1, col: 5, byte_idx: 8 },
                    Token { kind: Dedent, text: SmolStr::new("") },
                    Loc { line: 1, col: 5, byte_idx: 8 }
                )
            ],
        );
    }

    #[test]
    fn newline_token_location_3() {
        use smol_str::SmolStr;
        let input = "f(x())";
        let toks: Vec<(Loc, Token, Loc)> =
            scan(crate::lexer::lex(input, "test").into_iter(), "test");
        #[rustfmt::skip]
        assert_eq!(
            toks,
            [
                (
                    Loc { line: 0, col: 0, byte_idx: 0 },
                    Token { kind: LowerId, text: SmolStr::new("f") },
                    Loc { line: 0, col: 1, byte_idx: 1 }
                ),
                (
                    Loc { line: 0, col: 1, byte_idx: 1 },
                    Token { kind: LParen, text: SmolStr::new("(") },
                    Loc { line: 0, col: 2, byte_idx: 2 }
                ),
                (
                    Loc { line: 0, col: 2, byte_idx: 2 },
                    Token { kind: LowerId, text: SmolStr::new("x") },
                    Loc { line: 0, col: 3, byte_idx: 3 }
                ),
                (
                    Loc { line: 0, col: 3, byte_idx: 3 },
                    Token { kind: LParen, text: SmolStr::new("(") },
                    Loc { line: 0, col: 4, byte_idx: 4 }
                ),
                (
                    Loc { line: 0, col: 4, byte_idx: 4 },
                    Token { kind: RParen, text: SmolStr::new(")") },
                    Loc { line: 0, col: 5, byte_idx: 5 }
                ),
                (
                    Loc { line: 0, col: 5, byte_idx: 5 },
                    Token { kind: RParen, text: SmolStr::new(")") },
                    Loc { line: 0, col: 6, byte_idx: 6 }
                ),
                (
                    Loc { line: 0, col: 6, byte_idx: 6 },
                    Token { kind: Newline, text: SmolStr::new("") },
                    Loc { line: 0, col: 6, byte_idx: 6 }
                ),
            ],
        );
    }
}
