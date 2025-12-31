use crate::ast::{self, Id, L};

use smol_str::SmolStr;

pub(crate) fn parse_char_lit(text: &str) -> char {
    let mut chars = text.chars();

    let quote = chars.next(); // skip '
    debug_assert_eq!(quote, Some('\''));

    let char = chars.next().unwrap();
    if char == '\\' {
        match chars.next().unwrap() {
            '\'' => '\'',
            'n' => '\n',
            't' => '\t',
            'r' => '\r',
            '\\' => '\\',
            other => panic!("Unknown escaped character: '\\{other}'"),
        }
    } else {
        char
    }
}

pub(crate) fn parse_int_lit(
    mut text: &str,
    module: &std::rc::Rc<str>,
    loc: &lexgen_util::Loc,
) -> u64 {
    text = text.strip_prefix("-").unwrap_or(text);

    let mut base: u32 = 10;

    if text.starts_with("0b") {
        base = 2;
        text = &text[2..];
    } else if text.starts_with("0x") {
        base = 16;
        text = &text[2..];
    }

    // We can't use standard library `from_str_radix` or similar as we have to skip '_' characters.
    let mut value: u64 = 0;

    for char in text.chars() {
        if char == '_' {
            continue;
        }

        let digit: u32 = char.to_digit(base).unwrap_or_else(|| {
            panic!(
                "{}:{}:{}: invalid base {} digit: {}",
                module,
                loc.line + 1,
                loc.col + 1,
                base,
                char
            )
        });

        value = value.checked_mul(u64::from(base)).unwrap_or_else(|| {
            panic!(
                "{}:{}:{}: integer literal too large",
                module,
                loc.line + 1,
                loc.col + 1,
            )
        });

        value = value.checked_add(u64::from(digit)).unwrap_or_else(|| {
            panic!(
                "{}:{}:{}: integer literal too large",
                module,
                loc.line + 1,
                loc.col + 1,
            )
        });
    }

    value
}

pub(crate) fn process_param_list(
    params: Vec<(Id, Option<L<ast::Type>>)>,
    module: &std::rc::Rc<str>,
    loc: &lexgen_util::Loc,
) -> (ast::SelfParam, Vec<(Id, Option<L<ast::Type>>)>) {
    let mut self_param = ast::SelfParam::No;
    let mut typed_params: Vec<(Id, Option<L<ast::Type>>)> = Vec::with_capacity(params.len());

    for (param_id, param_ty) in params {
        if param_id == "self" {
            self_param = match param_ty {
                Some(self_ty) => ast::SelfParam::Explicit(self_ty),
                None => ast::SelfParam::Implicit,
            };
        } else {
            match param_ty {
                Some(ty) => typed_params.push((param_id, Some(ty))),
                None => panic!(
                    "{}:{}:{}: Parameter {} without type",
                    module,
                    loc.line + 1,
                    loc.col + 1,
                    param_id
                ),
            }
        }
    }

    (self_param, typed_params)
}

pub(crate) fn path_parts(path: &SmolStr) -> Vec<SmolStr> {
    let parts: Vec<SmolStr> = path.split('.').map(SmolStr::new).collect();
    assert_eq!(parts.len(), 2);
    parts
}

pub(crate) fn process_fields(
    fields: Vec<(Option<Id>, L<ast::Type>)>,
    module: &std::rc::Rc<str>,
    loc: &lexgen_util::Loc,
) -> ast::ConFields {
    if fields.is_empty() {
        return ast::ConFields::Empty;
    }

    let mut found_named = false;
    let mut found_unnamed = false;
    for (name, _) in fields.iter() {
        if name.is_some() {
            found_named = true;
        } else {
            found_unnamed = true;
        }
    }

    if found_named && found_unnamed {
        panic!(
            "{}:{}:{}: Field list cannot have both named and unnamed fields",
            module,
            loc.line + 1,
            loc.col + 1,
        );
    }

    if found_named {
        ast::ConFields::Named(fields.into_iter().map(|(n, t)| (n.unwrap(), t)).collect())
    } else {
        ast::ConFields::Unnamed(fields.into_iter().map(|(_, t)| t).collect())
    }
}
