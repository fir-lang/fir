use crate::ast;
use crate::name::Name;
use crate::token::Token;
use crate::utils::loc_display;

#[derive(Debug, Clone)]
pub enum StrPart {
    Str(String),
    Expr(ast::L<ast::Expr>),
}

pub(crate) fn str_parts(
    interpolations: Vec<(Token, ast::L<ast::Expr>)>,
    end: Token,
) -> Vec<StrPart> {
    let mut parts: Vec<StrPart> = Vec::with_capacity(1 + (interpolations.len() * 2));

    for (before, expr) in interpolations {
        // Drop the `
        let str = before.text.as_str();
        let str = &str[..str.len() - 1];
        parts.push(StrPart::Str(copy_update_escapes(str)));
        parts.push(StrPart::Expr(expr));
    }

    // Drop the "
    let str = end.text.as_str();
    let str = &str[..str.len() - 1];
    parts.push(StrPart::Str(copy_update_escapes(str)));

    parts
}

#[derive(Debug, Clone)]
pub enum ExternTypeTemplatePart {
    C(String),
    Var(ast::L<Name>),
}

pub(crate) fn extern_type_template_parts(
    interpolations: Vec<(Token, ast::L<ast::Expr>)>,
    end: Token,
) -> Vec<ExternTypeTemplatePart> {
    let mut parts: Vec<ExternTypeTemplatePart> = Vec::with_capacity(1 + (interpolations.len() * 2));

    for (before, expr) in interpolations {
        let ty_var = match expr.node {
            ast::Expr::Var(ast::VarExpr {
                mod_prefix,
                name,
                user_ty_args,
                ty_args: _,
                inferred_ty: _,
                resolved_id: _,
            }) if mod_prefix.is_none() && user_ty_args.is_empty() => name,

            _ => panic!(
                "{}: Extern type strings can only have type variables as interpolations",
                &loc_display(&expr.loc)
            ),
        };

        // Drop the `
        let str = before.text.as_str();
        let str = &str[..str.len() - 1];
        parts.push(ExternTypeTemplatePart::C(copy_update_escapes(str)));
        parts.push(ExternTypeTemplatePart::Var(ast::L {
            loc: expr.loc.clone(),
            node: ty_var,
        }));
    }

    // Drop the "
    let str = end.text.as_str();
    let str = &str[..str.len() - 1];
    parts.push(ExternTypeTemplatePart::C(copy_update_escapes(str)));

    parts
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
