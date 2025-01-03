use crate::ast::{self, Id, Loc};
use crate::collections::{Map, Set};
use crate::type_checker::{row_utils, PgmTypes, TcFunState, Ty, TyArgs};

use super::RecordOrVariant;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CoveredPats {
    cons: Map<Con, Fields>,
    records: Fields,
    variants: Map<Id, Fields>,
    matches_all: bool,
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
            ast::Pat::Var(_) | ast::Pat::Ignore => {
                self.matches_all = true;
            }

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

            ast::Pat::Str(_) | ast::Pat::Char(_) | ast::Pat::StrPfx(_, _) => {}
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

impl CoveredPats {
    /// Return whether the covered patterns cover all possibles values of `ty`.
    pub fn is_exhaustive(&self, ty: &Ty, tc_state: &mut TcFunState, loc: &Loc) -> bool {
        if self.matches_all {
            return true;
        }

        match ty.normalize(tc_state.tys.tys.cons()) {
            Ty::Con(ty_con) => match con_shape(&ty_con, &tc_state.tys) {
                ConShape::Product => {
                    let (con_fn_ty, con_fn_ty_args) = tc_state
                        .tys
                        .top_schemes
                        .get(&ty_con)
                        .unwrap()
                        .instantiate(0, tc_state.var_gen, tc_state.preds, loc);

                    // Scrutinee type doesn't have arguments.
                    assert!(con_fn_ty_args.is_empty());

                    self.is_con_pat_exhaustive(&con_fn_ty, &ty_con, None, tc_state, loc)
                }

                ConShape::Sum(cons) => {
                    for con in cons {
                        let (con_fn_ty, con_fn_ty_args) = tc_state
                            .tys
                            .associated_fn_schemes
                            .get(&ty_con)
                            .unwrap()
                            .get(&con)
                            .unwrap()
                            .instantiate(0, tc_state.var_gen, tc_state.preds, loc);

                        // Scrutinee type doesn't have arguments.
                        assert!(con_fn_ty_args.is_empty());

                        if !self.is_con_pat_exhaustive(
                            &con_fn_ty,
                            &ty_con,
                            Some(&con),
                            tc_state,
                            loc,
                        ) {
                            return false;
                        }
                    }

                    true
                }
            },

            Ty::App(ty_con, ty_args) => {
                let ty_args = match ty_args {
                    TyArgs::Positional(args) => args,
                    TyArgs::Named(_) => panic!(),
                };
                match con_shape(&ty_con, &tc_state.tys) {
                    ConShape::Product => {
                        let (con_fn_ty, con_fn_ty_args) = tc_state
                            .tys
                            .top_schemes
                            .get(&ty_con)
                            .unwrap()
                            .instantiate(0, tc_state.var_gen, tc_state.preds, loc);

                        assert_eq!(ty_args.len(), con_fn_ty_args.len());

                        for (ty_var, ty_arg) in con_fn_ty_args.iter().zip(ty_args.iter()) {
                            ty_var.set_link(ty_arg.clone());
                        }

                        self.is_con_pat_exhaustive(&con_fn_ty, &ty_con, None, tc_state, loc)
                    }

                    ConShape::Sum(cons) => {
                        for con in cons {
                            let (con_fn_ty, con_fn_ty_args) = tc_state
                                .tys
                                .associated_fn_schemes
                                .get(&ty_con)
                                .unwrap()
                                .get(&con)
                                .unwrap()
                                .instantiate(0, tc_state.var_gen, tc_state.preds, loc);

                            assert_eq!(ty_args.len(), con_fn_ty_args.len());

                            for (ty_var, ty_arg) in con_fn_ty_args.iter().zip(ty_args.iter()) {
                                ty_var.set_link(ty_arg.clone());
                            }

                            if !self.is_con_pat_exhaustive(
                                &con_fn_ty,
                                &ty_con,
                                Some(&con),
                                tc_state,
                                loc,
                            ) {
                                return false;
                            }
                        }

                        true
                    }
                }
            }

            Ty::Anonymous {
                labels,
                extension,
                kind: RecordOrVariant::Variant,
                is_row,
            } => {
                assert!(!is_row);
                let (labels, extension) = row_utils::collect_rows(
                    tc_state.tys.tys.cons(),
                    ty,
                    RecordOrVariant::Variant,
                    &labels,
                    extension.clone(),
                );

                if extension.is_some() {
                    assert!(!self.matches_all); // checked above
                    return false;
                }

                for (label, label_ty) in labels {
                    // label_ty will be a rigid record type
                    let label_fields = match &label_ty {
                        Ty::Anonymous {
                            labels,
                            extension,
                            kind,
                            is_row,
                        } => {
                            assert!(extension.is_none());
                            assert_eq!(*kind, RecordOrVariant::Record);
                            assert!(!is_row);
                            labels
                        }
                        _ => panic!(),
                    };

                    let field_pats: &Fields = match self.variants.get(&label) {
                        Some(label_pat) => label_pat,
                        None => return false,
                    };

                    for (field, field_ty) in label_fields {
                        match field_pats.named.get(field) {
                            Some(field_pat) => {
                                if !field_pat.is_exhaustive(&field_ty, tc_state, loc) {
                                    return false;
                                }
                            }
                            None => return false,
                        }
                    }
                }

                true
            }

            Ty::Anonymous {
                labels,
                extension,
                kind: RecordOrVariant::Record,
                is_row,
            } => {
                assert!(!is_row);
                let (labels, _extension) = row_utils::collect_rows(
                    tc_state.tys.tys.cons(),
                    ty,
                    RecordOrVariant::Record,
                    &labels,
                    extension.clone(),
                );

                for (label, label_ty) in labels {
                    match self.records.named.get(&label) {
                        Some(label_pats) => {
                            if !label_pats.is_exhaustive(&label_ty, tc_state, loc) {
                                return false;
                            }
                        }
                        None => return false,
                    }
                }

                true
            }

            Ty::Var(_) => false,

            Ty::QVar(_) | Ty::Fun(_, _) | Ty::FunNamedArgs(_, _) => panic!(),

            Ty::AssocTySelect { .. } => todo!(),
        }
    }

    fn is_con_pat_exhaustive(
        &self,
        con_fn_ty: &Ty,
        ty_con: &Id,
        con: Option<&Id>,
        tc_state: &mut TcFunState,
        loc: &Loc,
    ) -> bool {
        let con_field_pats = match self.cons.get(&Con {
            ty: ty_con.clone(),
            con: con.cloned(),
        }) {
            Some(fields) => fields,
            None => return false,
        };

        match con_fn_ty {
            Ty::Fun(args, _) => {
                // If we have a pattern for the constructor, it should have the
                // right number of fields.
                assert_eq!(args.len(), con_field_pats.unnamed.len());

                for (fun_arg, fun_arg_pat) in args.iter().zip(con_field_pats.unnamed.iter()) {
                    if !fun_arg_pat.is_exhaustive(fun_arg, tc_state, loc) {
                        return false;
                    }
                }

                true
            }

            Ty::FunNamedArgs(args, _) => {
                // Same as above.
                assert_eq!(
                    args.keys().collect::<Set<_>>(),
                    con_field_pats.named.keys().collect::<Set<_>>()
                );

                for (arg_name, arg_ty) in args.iter() {
                    if !con_field_pats
                        .named
                        .get(arg_name)
                        .unwrap()
                        .is_exhaustive(arg_ty, tc_state, loc)
                    {
                        return false;
                    }
                }

                true
            }

            Ty::App(_, _) | Ty::Con(_) => {
                // Constructor doesn't have fields.
                assert!(con_field_pats.named.is_empty());
                assert!(con_field_pats.unnamed.is_empty());
                true
            }

            other => panic!("{:?}", other),
        }
    }
}

#[derive(Debug, Clone)]
enum ConShape {
    Product,
    Sum(Vec<Id>),
}

fn con_shape(ty_con: &Id, tys: &PgmTypes) -> ConShape {
    let cons = tys.tys.get_con(ty_con).unwrap().con_details().unwrap();
    if cons.len() == 1 {
        ConShape::Product
    } else {
        ConShape::Sum(cons.iter().map(|con| con.name.clone().unwrap()).collect())
    }
}
