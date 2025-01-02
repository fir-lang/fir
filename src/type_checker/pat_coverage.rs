use crate::ast::{self, Id};
use crate::collections::Map;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CoveredPats {
    cons: Map<Con, Fields>,
    records: Fields,
    variants: Map<Id, Fields>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct Fields {
    named: Map<Id, CoveredPats>,
    unnamed: Vec<CoveredPats>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Con {
    ty: Id,
    con: Option<Id>,
}

impl Con {
    fn from_ast_con(con: &ast::Constructor) -> Self {
        Con {
            ty: con.type_.clone(),
            con: con.constr.clone(),
        }
    }
}

impl CoveredPats {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn add(&mut self, pat: &ast::Pat) {
        match pat {
            ast::Pat::Var(_) => {}

            ast::Pat::Constr(ast::ConstrPattern {
                constr,
                fields,
                ty_args: _,
            }) => {
                let con = Con::from_ast_con(constr);
                let field_pats = self.cons.entry(con).or_default();
                for (field_idx, field) in fields.iter().enumerate() {
                    match &field.name {
                        Some(field_name) => field_pats
                            .named
                            .entry(field_name.clone())
                            .or_default()
                            .add(&field.node.node),
                        None => {
                            if field_pats.unnamed.len() <= field_idx {
                                field_pats.unnamed.resize(field_idx + 1, Default::default());
                            }
                            field_pats.unnamed[field_idx].add(&field.node.node);
                        }
                    }
                }
            }

            ast::Pat::Variant(ast::VariantPattern { constr, fields }) => {
                let variant_pats = self.variants.entry(constr.clone()).or_default();
                variant_pats.add(fields);
            }

            ast::Pat::Record(fields) => {
                self.records.add(fields);
            }

            ast::Pat::Or(l1, l2) => {
                self.add(&l1.node);
                self.add(&l2.node);
            }

            ast::Pat::Ignore | ast::Pat::Str(_) | ast::Pat::Char(_) | ast::Pat::StrPfx(_, _) => {}
        }
    }
}

impl Fields {
    fn add(&mut self, fields: &[ast::Named<ast::L<ast::Pat>>]) {
        for (field_idx, field) in fields.iter().enumerate() {
            match &field.name {
                Some(field_name) => self
                    .named
                    .entry(field_name.clone())
                    .or_default()
                    .add(&field.node.node),
                None => {
                    if self.unnamed.len() <= field_idx {
                        self.unnamed.resize(field_idx + 1, Default::default());
                    }
                    self.unnamed[field_idx].add(&field.node.node);
                }
            }
        }
    }
}
