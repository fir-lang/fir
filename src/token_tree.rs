#![allow(unused)]

use crate::token::{Token, TokenKind};

use std::iter::Peekable;

use lexgen_util::Loc;

pub type TokenTree = Vec<TokenTreeNode>;

/// A single token, or a delimited list of token trees.
#[derive(Debug, Clone)]
pub enum TokenTreeNode {
    /// A single token.
    Single(Single),

    /// A delimited list of token trees.
    Delimited(Delimited),
}

#[derive(Debug, Clone)]
pub struct Single {
    pub left: Loc,
    pub token: Token,
    pub right: Loc,
}

/// A delimited list of token trees.
#[derive(Debug, Clone)]
pub struct Delimited {
    /// The delimiter: parens, brackets, or braces.
    pub delim: Delimiter,

    /// Location of the delimiter on the left.
    pub left_delim: Loc,

    /// Location of the delimiter on the right.
    pub right_delim: Loc,

    /// The elements in the group, separated by commas or semicolons.
    pub elems: Vec<TokenTreeSep>,
}

/// A token tree in a delimited group.
///
/// `TokenTreeSep`s are separated by a comma or semicolon. The last `TokenTreeSep` in a delimited
/// group may not have a comma or semicolon.
#[derive(Debug, Clone)]
pub struct TokenTreeSep {
    /// The tokens in a delimited group.
    pub tokens: TokenTree,

    /// The separator after the tokens. This may be `None` when the tokens are the last in the
    /// delimited group.
    pub sep: Option<Separator>,
}

/// A separator in a `TokenTreeSep`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Separator {
    /// Kind of the separator: comma or semicolon.
    pub kind: SeparatorKind,

    /// Location of the separator.
    pub loc: Loc,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Delimiter {
    Brace,
    Bracket,
    Paren,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SeparatorKind {
    Comma,
    Semicolon,
}

pub fn tokens_to_tree<I>(module: &str, tokens: &mut Peekable<I>) -> TokenTree
where
    I: Iterator<Item = (Loc, Token, Loc)>,
{
    let mut root: TokenTree = vec![];

    while let Some(token) = tokens.next() {
        match token.1.kind {
            TokenKind::LParen | TokenKind::LBrace | TokenKind::LBracket => {
                let delim = match token.1.kind {
                    TokenKind::LParen => Delimiter::Paren,
                    TokenKind::LBrace => Delimiter::Brace,
                    TokenKind::LBracket => Delimiter::Bracket,
                    _ => unreachable!(),
                };
                let (elems, right_delim) = parse_delimited(module, tokens, delim);
                root.push(TokenTreeNode::Delimited(Delimited {
                    delim,
                    left_delim: token.0,
                    right_delim,
                    elems,
                }))
            }

            _ => {
                root.push(TokenTreeNode::Single(Single {
                    left: token.0,
                    token: token.1,
                    right: token.2,
                }));
            }
        }
    }

    root
}

fn parse_delimited<I>(
    module: &str,
    tokens: &mut Peekable<I>,
    delim: Delimiter,
) -> (Vec<TokenTreeSep>, Loc)
where
    I: Iterator<Item = (Loc, Token, Loc)>,
{
    let mut elems: Vec<TokenTreeSep> = vec![];

    let mut current_elem: TokenTree = vec![];

    for token in tokens.by_ref() {
        match token.1.kind {
            TokenKind::Comma | TokenKind::Semicolon => {
                elems.push(TokenTreeSep {
                    tokens: std::mem::take(&mut current_elem),
                    sep: Some(Separator {
                        kind: if token.1.kind == TokenKind::Comma {
                            SeparatorKind::Comma
                        } else {
                            SeparatorKind::Semicolon
                        },
                        loc: token.0,
                    }),
                });
            }

            TokenKind::RParen | TokenKind::RBrace | TokenKind::RBracket => {
                if (delim == Delimiter::Paren && token.1.kind == TokenKind::RParen)
                    || (delim == Delimiter::Brace && token.1.kind == TokenKind::RBrace)
                    || (delim == Delimiter::Bracket && token.1.kind == TokenKind::RBracket)
                {
                    if !current_elem.is_empty() {
                        elems.push(TokenTreeSep {
                            tokens: std::mem::take(&mut current_elem),
                            sep: None,
                        });
                    }
                    return (elems, token.0);
                } else {
                    panic!(
                        "{}:{}:{}: Unexpected '{}'",
                        module,
                        token.0.line,
                        token.0.col,
                        match token.1.kind {
                            TokenKind::RParen => ')',
                            TokenKind::RBrace => '}',
                            TokenKind::RBracket => ']',
                            _ => unreachable!(),
                        }
                    );
                }
            }

            _ => {
                current_elem.push(TokenTreeNode::Single(Single {
                    left: token.0,
                    token: token.1,
                    right: token.2,
                }));
            }
        }
    }

    panic!(
        "{}: Unterminated '{}'",
        module,
        match delim {
            Delimiter::Brace => '{',
            Delimiter::Paren => '(',
            Delimiter::Bracket => '[',
        },
    );
}

pub fn tree_to_tokens(token_tree: TokenTree) -> Vec<(Loc, Token, Loc)> {
    let mut tokens: Vec<(Loc, Token, Loc)> = vec![];
    tree_to_tokens_(token_tree, &mut tokens);
    tokens
}

fn tree_to_tokens_(token_tree: TokenTree, tokens: &mut Vec<(Loc, Token, Loc)>) {
    for node in token_tree {
        node_to_tokens(node, tokens);
    }
}

fn node_to_tokens(node: TokenTreeNode, tokens: &mut Vec<(Loc, Token, Loc)>) {
    match node {
        TokenTreeNode::Single(Single { left, token, right }) => tokens.push((left, token, right)),
        TokenTreeNode::Delimited(Delimited {
            delim,
            left_delim,
            right_delim,
            elems,
        }) => {
            let (left_delim_tok, right_delim_tok) = match delim {
                Delimiter::Brace => (Token::lbrace(), Token::rbrace()),
                Delimiter::Bracket => (Token::lbracket(), Token::rbracket()),
                Delimiter::Paren => (Token::lparen(), Token::rparen()),
            };
            tokens.push((left_delim, left_delim_tok, loc1(&left_delim)));
            for elem in elems {
                token_tree_sep_to_tokens(elem, tokens);
            }
            tokens.push((right_delim, right_delim_tok, loc1(&right_delim)));
        }
    }
}

fn token_tree_sep_to_tokens(
    TokenTreeSep { tokens, sep }: TokenTreeSep,
    out: &mut Vec<(Loc, Token, Loc)>,
) {
    tree_to_tokens_(tokens, out);
    if let Some(sep) = sep {
        let tok = match sep.kind {
            SeparatorKind::Comma => Token::comma(),
            SeparatorKind::Semicolon => Token::semicolon(),
        };
        out.push((sep.loc, tok, loc1(&sep.loc)));
    }
}

fn loc1(loc: &Loc) -> Loc {
    Loc {
        line: loc.line,
        col: loc.col + 1,
        byte_idx: loc.byte_idx + 1,
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::lexer::lex;

    use indoc::indoc;

    #[test]
    fn token_tree_roundtrip_1() {
        let tokens0 = lex(
            indoc! {"
                fn test(a, b,) {
                    stmt1
                    stmt2
                } [1, 2,,]
            "},
            "test",
        );
        let tree = tokens_to_tree("test", &mut tokens0.clone().into_iter().peekable());
        let tokens1 = tree_to_tokens(tree.clone());
        assert_eq!(tokens0, tokens1);
    }

    #[test]
    fn token_tree_roundtrip_2() {
        let tokens0 = lex(
            indoc! {"
                (1, fn()
                    a
                    b, 3)
            "},
            "test",
        );
        let tree = tokens_to_tree("test", &mut tokens0.clone().into_iter().peekable());
        let tokens1 = tree_to_tokens(tree.clone());
        assert_eq!(tokens0, tokens1);
    }
}
