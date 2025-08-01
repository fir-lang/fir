use crate::ast::{self, Id, Loc};
use crate::collections::{Map, Set};
use crate::type_checker::{FunArgs, TcFunState, Ty, TyMap, row_utils};

use super::RecordOrVariant;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct PatCoverage {
    cons: Map<Con, Fields>,
    records: Fields,
    matches_all: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Fields {
    named: Map<Id, PatCoverage>,
    unnamed: Vec<PatCoverage>,
    ignore_rest: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Con {
    ty: Id,
    con: Option<Id>,
}

impl Con {
    fn from_ast_con(con: &ast::Constructor) -> Self {
        Con {
            ty: con.ty.clone(),
            con: con.constr.clone(),
        }
    }
}

impl PatCoverage {
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
                ignore_rest: _,
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

            ast::Pat::Record(ast::RecordPattern {
                fields,
                ignore_rest,
                inferred_ty: _,
            }) => {
                self.records.ignore_rest |= *ignore_rest;
                self.records.add(fields);
            }

            ast::Pat::Or(l1, l2) => {
                self.add(&l1.node);
                self.add(&l2.node);
            }

            ast::Pat::Str(_) | ast::Pat::Char(_) | ast::Pat::StrPfx(_, _) => {}
        }
    }

    pub fn get_con_fields(&self, ty: &Id, con: Option<&Id>) -> Option<&Fields> {
        self.cons.get(&Con {
            ty: ty.clone(),
            con: con.cloned(),
        })
    }

    pub fn get_record_field(&self, field: &Id) -> Option<&PatCoverage> {
        self.records.named.get(field)
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

impl PatCoverage {
    /// Return whether the covered patterns cover all possibles values of `ty`.
    pub fn is_exhaustive(&self, ty: &Ty, tc_state: &mut TcFunState, loc: &Loc) -> bool {
        if self.matches_all {
            return true;
        }

        match ty.normalize(tc_state.tys.tys.cons()) {
            Ty::Con(ty_con, _) => match con_shape(&ty_con, &tc_state.tys.tys) {
                ConShape::Product => {
                    let con_scheme = tc_state.tys.top_schemes.get(&ty_con).unwrap();
                    let con_fn_ty = con_scheme.instantiate_with_tys(&[], tc_state.preds, loc);
                    self.is_con_pat_exhaustive(&con_fn_ty, &ty_con, None, tc_state, loc)
                }

                ConShape::Sum(cons) => {
                    for con in cons {
                        let con_scheme = tc_state
                            .tys
                            .associated_fn_schemes
                            .get(&ty_con)
                            .unwrap()
                            .get(&con)
                            .unwrap();

                        let con_fn_ty = con_scheme.instantiate_with_tys(&[], tc_state.preds, loc);

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

            Ty::App(ty_con, ty_args, _) => match con_shape(&ty_con, &tc_state.tys.tys) {
                ConShape::Product => {
                    let con_scheme = tc_state.tys.top_schemes.get(&ty_con).unwrap();
                    let con_fn_ty = con_scheme.instantiate_with_tys(&ty_args, tc_state.preds, loc);
                    self.is_con_pat_exhaustive(&con_fn_ty, &ty_con, None, tc_state, loc)
                }

                ConShape::Sum(cons) => {
                    for con in cons {
                        let con_scheme = tc_state
                            .tys
                            .associated_fn_schemes
                            .get(&ty_con)
                            .unwrap()
                            .get(&con)
                            .unwrap();

                        let con_fn_ty =
                            con_scheme.instantiate_with_tys(&ty_args, tc_state.preds, loc);

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

                for label_ty in labels.values() {
                    // `label` is a fully qualified name of a type, and `label_ty` is a value
                    // of the type.
                    if !self.is_exhaustive(label_ty, tc_state, loc) {
                        return false;
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
                        None => {
                            if !self.records.ignore_rest {
                                return false;
                            }
                        }
                    }
                }

                true
            }

            Ty::Var(_) => false,

            Ty::QVar(_, _) | Ty::Fun { .. } => panic!(),
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
            Ty::Fun {
                args,
                ret: _,
                exceptions: _,
            } => {
                match args {
                    FunArgs::Positional(args) => {
                        // The constructor can have more fields than the pattern, extra fields in
                        // the pattern are ignored with `..`.
                        assert!(con_field_pats.unnamed.len() <= args.len());

                        for (fun_arg, fun_arg_pat) in args.iter().zip(con_field_pats.unnamed.iter())
                        {
                            if !fun_arg_pat.is_exhaustive(fun_arg, tc_state, loc) {
                                return false;
                            }
                        }
                    }

                    FunArgs::Named(args) => {
                        // Same as above.
                        assert!(
                            con_field_pats
                                .named
                                .keys()
                                .collect::<Set<_>>()
                                .is_subset(&args.keys().collect::<Set<_>>())
                        );

                        for (arg_name, arg_ty) in args.iter() {
                            let field_pat = match con_field_pats.named.get(arg_name) {
                                Some(field_pat) => field_pat,
                                None => continue,
                            };

                            if !field_pat.is_exhaustive(arg_ty, tc_state, loc) {
                                return false;
                            }
                        }
                    }
                }

                true
            }

            Ty::App(_, _, _) | Ty::Con(_, _) => {
                // Constructor doesn't have fields.
                assert!(con_field_pats.named.is_empty());
                assert!(con_field_pats.unnamed.is_empty());
                true
            }

            other => panic!("{other:?}"),
        }
    }
}

#[derive(Debug, Clone)]
enum ConShape {
    Product,
    Sum(Vec<Id>),
}

fn con_shape(ty_con: &Id, tys: &TyMap) -> ConShape {
    let ty_details = tys.get_con(ty_con).unwrap().con_details().unwrap();
    if ty_details.sum {
        ConShape::Sum(
            ty_details
                .cons
                .iter()
                .map(|con| con.name.clone().unwrap())
                .collect(),
        )
    } else {
        ConShape::Product
    }
}

impl Fields {
    pub fn get_named_field(&self, name: &Id) -> Option<&PatCoverage> {
        self.named.get(name)
    }

    pub fn get_positional_field(&self, idx: usize) -> Option<&PatCoverage> {
        self.unnamed.get(idx)
    }
}
