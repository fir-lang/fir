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
    scan_indented(
        &mut tokens,
        module,
        &mut new_tokens,
        Loc {
            line: 0,
            col: 0,
            byte_idx: 0,
        },
        IndentedDelimKind::File,
    );
    assert!(tokens.next().is_none());
    new_tokens
}

pub enum IndentedDelimKind {
    File,
    Brace,
}

/// Scan an indented block: a file or `{...}` block.
///
/// When scanning a `{...}`, the `{` should be consumed in `tokens`.
pub fn scan_indented<I>(
    tokens: &mut Peekable<I>,
    module: &str,
    new_tokens: &mut Vec<(Loc, Token, Loc)>,
    ldelim_loc: Loc,
    delim_kind: IndentedDelimKind,
) -> Loc
where
    I: Iterator<Item = (Loc, Token, Loc)>,
{
    // println!(
    //     "Starting indented block at {}:{}",
    //     ldelim_loc.line + 1,
    //     ldelim_loc.col + 1
    // );

    if tokens.peek().is_none() {
        match delim_kind {
            IndentedDelimKind::File => {
                return Loc {
                    line: 0,
                    col: 0,
                    byte_idx: 0,
                }
            }
            IndentedDelimKind::Brace => {
                panic!(
                    "{}:{}:{}: Unterminated '{{'",
                    module,
                    ldelim_loc.line + 1,
                    ldelim_loc.col + 1
                );
            }
        }
    }

    let mut last_loc: Loc = tokens.peek().unwrap().0;
    let mut indent_stack: Vec<u32> = vec![last_loc.col];

    // Only generate `INDENT` after a `:`.
    let mut generate_indent = false;

    while let Some((l, t, r)) = tokens.next() {
        if matches!(t.kind, TokenKind::RBrace) {
            // Terminate the last statement.
            if !matches!(
                new_tokens.last(),
                Some((
                    _,
                    Token {
                        kind: TokenKind::Newline,
                        ..
                    },
                    _
                ))
            ) {
                new_tokens.push(newline(last_loc));
            }

            // Terminate open blocks.
            // Note that because we don't generate an `INDENT` after `{`, we shouldn't generate a
            // `DEDENT` for top indentation level.
            while indent_stack.len() > 1 {
                indent_stack.pop();
                new_tokens.push(dedent(l));
            }

            // Finally push the '}'
            new_tokens.push((l, t, r));

            // println!("Ending indented block at {}:{}", l.line + 1, l.col + 1);
            return r;
        }

        if l.line != last_loc.line {
            // Generate indentation tokens.
            let last_indent = *indent_stack.last().unwrap();
            match l.col.cmp(&last_indent) {
                Ordering::Greater => {
                    if generate_indent {
                        indent_stack.push(l.col);
                        new_tokens.push(newline(l));
                        new_tokens.push(indent(l));
                    }
                }

                Ordering::Equal => {
                    // Generate a newline at the last line.
                    new_tokens.push(newline(last_loc));
                }

                Ordering::Less => {
                    new_tokens.push(newline(last_loc));
                    loop {
                        indent_stack.pop();
                        new_tokens.push(dedent(last_loc));
                        if let Some(next) = indent_stack.last() {
                            if l.col >= *next {
                                break;
                            }
                        } else {
                            break;
                        }
                    }
                }
            }
        }

        last_loc = r;

        let kind = t.kind;
        new_tokens.push((l, t, r));

        generate_indent = false;

        match kind {
            TokenKind::LParen | TokenKind::LParenRow => {
                scan_non_indented(tokens, module, new_tokens, l, NonIndentedDelimKind::Paren);
            }

            TokenKind::LBracket | TokenKind::LBracketRow => {
                scan_non_indented(tokens, module, new_tokens, l, NonIndentedDelimKind::Bracket);
            }

            TokenKind::LBrace => {
                scan_indented(tokens, module, new_tokens, l, IndentedDelimKind::Brace);
            }

            TokenKind::RParen => {
                panic!(
                    "{}:{}:{}: ')' without matching '('",
                    module,
                    l.line + 1,
                    l.col + 1
                );
            }

            TokenKind::RBracket => {
                panic!(
                    "{}:{}:{}: ']' without matching '['",
                    module,
                    l.line + 1,
                    l.col + 1
                );
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
                generate_indent = true;
            }

            _ => {}
        }
    }

    // When scanning a file we won't see a token that termintes the block, the loop will terminate
    // instead to indicate "EOF". Generate DEDENTs as usual.
    new_tokens.push(newline(last_loc));
    while indent_stack.len() > 1 {
        indent_stack.pop();
        new_tokens.push(dedent(last_loc));
    }
    last_loc
}

pub enum NonIndentedDelimKind {
    Paren,
    Bracket,
}

/// Scan a non-indented block: `(...)` or `[...]`.
pub fn scan_non_indented<I>(
    tokens: &mut Peekable<I>,
    module: &str,
    new_tokens: &mut Vec<(Loc, Token, Loc)>,
    ldelim_loc: Loc,
    delim_kind: NonIndentedDelimKind,
) -> Loc
where
    I: Iterator<Item = (Loc, Token, Loc)>,
{
    // println!(
    //     "Starting non-indented block at {}:{}",
    //     ldelim_loc.line + 1,
    //     ldelim_loc.col + 1
    // );

    let mut last_loc = ldelim_loc;

    while let Some((l, t, r)) = tokens.next() {
        last_loc = r;

        match t.kind {
            TokenKind::RParen => match delim_kind {
                NonIndentedDelimKind::Paren => {
                    new_tokens.push((l, t, r));
                    // println!("Ending non-indented block at {}:{}", l.line + 1, l.col + 1);
                    return last_loc;
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
                    new_tokens.push((l, t, r));
                    // println!("Ending non-indented block at {}:{}", l.line + 1, l.col + 1);
                    return last_loc;
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

            TokenKind::LParen | TokenKind::LParenRow => {
                new_tokens.push((l, t, r));
                scan_non_indented(tokens, module, new_tokens, l, NonIndentedDelimKind::Paren);
            }

            TokenKind::LBracket | TokenKind::LBracketRow => {
                new_tokens.push((l, t, r));
                scan_non_indented(tokens, module, new_tokens, l, NonIndentedDelimKind::Bracket);
            }

            TokenKind::LBrace => {
                new_tokens.push((l, t, r));
                scan_indented(tokens, module, new_tokens, l, IndentedDelimKind::Brace);
            }

            TokenKind::RBrace => {
                panic!(
                    "{}:{}:{}: '}}' without matching '{{'",
                    module,
                    l.line + 1,
                    l.col + 1
                );
            }

            _ => {
                new_tokens.push((l, t, r));
            }
        }
    }

    last_loc
}

fn newline(loc: Loc) -> (Loc, Token, Loc) {
    (
        loc,
        Token {
            kind: TokenKind::Newline,
            text: "".into(),
        },
        loc,
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
                Newline,
                Indent,
                    LowerId, // a
                    Newline,
                    LowerId, // b
                    Newline,
                Dedent,
                RBrace,
                Newline,
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
    fn newline_token_location() {
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
}
