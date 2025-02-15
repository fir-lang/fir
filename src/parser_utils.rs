use crate::ast::{self, Id, L};

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
            other => panic!("Unknown escaped character: '\\{}'", other),
        }
    } else {
        char
    }
}

pub(crate) fn process_param_list(
    params: Vec<(Id, Option<L<ast::Type>>)>,
    module: &std::rc::Rc<str>,
    loc: &lexgen_util::Loc,
) -> (ast::SelfParam, Vec<(Id, L<ast::Type>)>) {
    let mut self_param = ast::SelfParam::No;
    let mut typed_params: Vec<(Id, L<ast::Type>)> = Vec::with_capacity(params.len());

    for (param_id, param_ty) in params {
        if param_id == "self" {
            self_param = match param_ty {
                Some(self_ty) => ast::SelfParam::Explicit(self_ty),
                None => ast::SelfParam::Implicit,
            };
        } else {
            match param_ty {
                Some(ty) => typed_params.push((param_id, ty)),
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
