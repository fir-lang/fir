use crate::token::{Token, TokenKind};

use std::cmp::Ordering;

use lexgen_util::Loc;

pub fn scan(tokens: Vec<(Loc, Token, Loc)>, module: &str) -> Vec<(Loc, Token, Loc)> {
    if tokens.is_empty() {
        return vec![];
    }

    let mut new_tokens: Vec<(Loc, Token, Loc)> = Vec::with_capacity(tokens.len() * 2);
    let mut indent_stack: Vec<u32> = vec![0];

    let mut last_loc = tokens[0].0;
    let mut delimiter_stack: Vec<Delimiter> = vec![];

    // Skip the indentation tokens after a backlash.
    let mut skip_indent = false;

    for (l, token, r) in tokens {
        let token_kind = token.kind;

        if token_kind == TokenKind::Backslash {
            // TODO: We should probably check that the next line should be on a new line, but it's
            // OK to just skip indentation token generation for now.
            skip_indent = true;
            continue;
        }

        if matches!(delimiter_stack.last(), None | Some(Delimiter::Brace))
            && l.line != last_loc.line
            && !skip_indent
        {
            // Generate a newline at the last line.
            new_tokens.push((
                last_loc,
                Token {
                    kind: TokenKind::Newline,
                    text: "".into(),
                },
                last_loc,
            ));

            // Generate indentation tokens.
            loop {
                let last_indent = *indent_stack.last().unwrap();
                match l.col.cmp(&last_indent) {
                    Ordering::Greater => {
                        indent_stack.push(l.col);
                        new_tokens.push((
                            l,
                            Token {
                                kind: TokenKind::Indent,
                                text: "".into(),
                            },
                            l,
                        ));
                        break;
                    }

                    Ordering::Equal => {
                        break;
                    }

                    Ordering::Less => {
                        indent_stack.pop();
                        new_tokens.push((
                            l,
                            Token {
                                kind: TokenKind::Dedent,
                                text: "".into(),
                            },
                            l,
                        ));
                    }
                }
            }
        }

        last_loc = r;

        match token_kind {
            TokenKind::LParen | TokenKind::LParenRow => delimiter_stack.push(Delimiter::Paren),
            TokenKind::LBracket | TokenKind::LBracketRow => {
                delimiter_stack.push(Delimiter::Bracket)
            }
            TokenKind::LBrace => delimiter_stack.push(Delimiter::Brace),

            TokenKind::RParen => {
                if delimiter_stack.pop() != Some(Delimiter::Paren) {
                    panic!(
                        "{}:{}:{}: ')' without matching '('",
                        module,
                        l.line + 1,
                        l.col + 1
                    );
                }
            }

            TokenKind::RBracket => {
                if delimiter_stack.pop() != Some(Delimiter::Bracket) {
                    panic!(
                        "{}:{}:{}: ']' without matching '['",
                        module,
                        l.line + 1,
                        l.col + 1
                    );
                }
            }

            TokenKind::RBrace => {
                if delimiter_stack.pop() != Some(Delimiter::Brace) {
                    panic!(
                        "{}:{}:{}: '}}' without matching '{{'",
                        module,
                        l.line + 1,
                        l.col + 1
                    );
                }
            }

            _ => {}
        }

        new_tokens.push((l, token, r));

        skip_indent = false;
    }

    // Python 3 seems to always generate a NEWLINE at the end before DEDENTs, even when the line
    // doesn't have a '\n' at the end, probably to terminate the last statement?
    let l = new_tokens.last().unwrap().2;
    new_tokens.push((
        l,
        Token {
            kind: TokenKind::Newline,
            text: "".into(),
        },
        l,
    ));

    // Terminate open blocks at the end.
    while let Some(indent) = indent_stack.pop() {
        if indent == 0 {
            assert!(indent_stack.is_empty());
            break;
        }

        new_tokens.push((
            l,
            Token {
                kind: TokenKind::Dedent,
                text: "".into(),
            },
            l,
        ));
    }

    new_tokens
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Delimiter {
    Paren,
    Bracket,
    Brace,
}

#[cfg(test)]
mod tests {
    use super::*;
    use TokenKind::*;

    use indoc::indoc;

    fn scan_wo_locs(input: &str) -> Vec<TokenKind> {
        scan(crate::lexer::lex(input, "test"), "test")
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
                Newline,
                Indent,
                LowerId, // b
                Newline,
                LowerId, // c
                Newline,
                Dedent,
                LowerId, // d
                Newline,
            ]
        );
    }

    #[test]
    fn dedent_multiple() {
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
                Newline,
                Indent,
                LowerId, // b
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
            a
                b
                    c
        "};
        let toks = scan_wo_locs(input);
        #[rustfmt::skip]
        assert_eq!(
            toks,
            vec![
                LowerId, // a
                Newline,
                Indent,
                LowerId, // b
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
}
