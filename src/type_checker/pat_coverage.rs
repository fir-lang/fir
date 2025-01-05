use crate::ast::{self, Id, Loc};
use crate::collections::{Map, Set};
use crate::type_checker::{row_utils, ty, PgmTypes, TcFunState, Ty, TyArgs};
use crate::utils::loc_display;

use super::RecordOrVariant;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct PatCoverage {
    cons: Map<Con, Fields>,
    records: Fields,
    variants: Map<Id, Fields>,
    matches_all: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Fields {
    named: Map<Id, PatCoverage>,
    unnamed: Vec<PatCoverage>,
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

    pub fn get_con_fields(&self, ty: &Id, con: Option<&Id>) -> Option<&Fields> {
        self.cons.get(&Con {
            ty: ty.clone(),
            con: con.cloned(),
        })
    }

    pub fn get_variant_fields(&self, con: &Id) -> Option<&Fields> {
        self.variants.get(con)
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
            Ty::Con(ty_con) => match con_shape(&ty_con, tc_state.tys) {
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
                match con_shape(&ty_con, tc_state.tys) {
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
                                if !field_pat.is_exhaustive(field_ty, tc_state, loc) {
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

    pub fn covers_variant(
        &self,
        label: &Id,
        field: &Ty,
        tc_state: &mut TcFunState,
        loc: &Loc,
    ) -> bool {
        // label_ty will be a rigid record type
        let label_fields = match &field {
            Ty::Anonymous {
                labels,
                extension,
                kind,
                is_row,
            } => {
                assert_eq!(*kind, RecordOrVariant::Record);
                assert!(extension.is_none());
                assert!(!is_row);
                labels
            }
            _ => panic!(),
        };

        let field_pats: &Fields = match self.variants.get(label) {
            Some(label_pat) => label_pat,
            None => return false,
        };

        for (field, field_ty) in label_fields {
            match field_pats.named.get(field) {
                Some(field_pat) => {
                    if !field_pat.is_exhaustive(field_ty, tc_state, loc) {
                        return false;
                    }
                }
                None => return false,
            }
        }

        true
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

/// Refine variant types in a scrutinee type (`ty`) based on the patterns covered (`coverage`).
///
/// Returns a new type with updated variants, and a `bool` indicating whether the type is fully
/// covered by the patterns.
pub fn refine_variants(ty: &Ty, coverage: &PatCoverage, tys: &PgmTypes, loc: &Loc) -> (Ty, bool) {
    let ty = ty.normalize(tys.tys.cons());
    match ty {
        Ty::App(ty_con_id, args) => {
            let ty_con = tys.tys.get_con(&ty_con_id).unwrap();
            let con_shapes: &[ty::ConShape] = match ty_con.con_details() {
                Some(details) => details,
                None => return (Ty::App(ty_con_id, args), false),
            };
            if con_shapes.is_empty() {
                return (Ty::App(ty_con_id, args), false);
            }

            /*
            TODO:

            We need to map constructor fields to type parameters of the type. E.g.

            type Blah[T1, T2]:
                A(I32, T1)
                B(T2, Str)
                C(T1, T2)

            To be able to keep track of covered labels in `T1`, we need to know that `T1` is used in these
            positions:

                A(_ , <>)
                C(<>, _ )

            If e.g. labels X and Y are covered in these positions, then we can refine the scrutinee type from
            `Blah[[X, Y, Z], ...]` to `Blah[[Z], ...]`.
            */

            for con in con_shapes {
                let con_ = Con {
                    ty: ty_con_id.clone(),
                    con: con.name.clone(),
                };
                let con_field_pats = match coverage.cons.get(&con_) {
                    Some(field_pats) => field_pats,
                    None => todo!(),
                };
                match &con.fields {
                    ty::ConFieldShape::Unnamed(arity) => {
                        // TODO
                    }
                    ty::ConFieldShape::Named(names) => {
                        // TODO
                    }
                }
                todo!()
            }

            // if ty_con_details
            todo!()
        }

        Ty::Anonymous {
            labels,
            extension,
            kind: RecordOrVariant::Variant,
            is_row,
        } => {
            assert!(!is_row);

            if coverage.matches_all {
                return (Ty::empty_variant(), true);
            }

            let mut unhandled_labels: Map<Id, Ty> =
                Map::with_capacity_and_hasher(labels.len(), Default::default());

            'next_variant_label: for (label, label_ty) in labels {
                match coverage.variants.get(&label) {
                    Some(label_field_pats) => match &label_ty {
                        Ty::Anonymous {
                            labels,
                            extension,
                            kind,
                            is_row,
                        } => {
                            assert!(!is_row);
                            assert_eq!(*kind, RecordOrVariant::Record);
                            assert!(extension.is_none());
                            let mut all_fields_covered = true;
                            let mut new_labels: Map<Id, Ty> =
                                Map::with_capacity_and_hasher(labels.len(), Default::default());
                            for (field_id, field_ty) in labels {
                                match label_field_pats.named.get(field_id) {
                                    Some(field_pat_coverage) => {
                                        let (field_ty, field_covered) =
                                            refine_variants(field_ty, field_pat_coverage, tys, loc);
                                        all_fields_covered &= field_covered;
                                        new_labels.insert(field_id.clone(), field_ty);
                                    }
                                    None => {
                                        unhandled_labels.insert(label, label_ty);
                                        continue 'next_variant_label;
                                    }
                                }
                            }
                            if !all_fields_covered {
                                let new_label_ty = Ty::Anonymous {
                                    labels: new_labels,
                                    extension: None,
                                    kind: RecordOrVariant::Record,
                                    is_row: false,
                                };
                                unhandled_labels.insert(label, new_label_ty);
                            }
                        }
                        _ => {
                            unhandled_labels.insert(label, label_ty);
                        }
                    },
                    None => {
                        unhandled_labels.insert(label, label_ty);
                    }
                }
            }

            let empty = unhandled_labels.is_empty() && extension.is_none();
            let new_variant = Ty::Anonymous {
                labels: unhandled_labels,
                extension,
                kind: RecordOrVariant::Variant,
                is_row: false,
            };

            (new_variant, empty)
        }

        Ty::Anonymous {
            labels,
            extension,
            kind: RecordOrVariant::Record,
            is_row,
        } => todo!(),

        Ty::QVar(_) => panic!("{}: BUG: QVar in refine_variants", loc_display(loc)),

        Ty::Var(_)
        | Ty::Con(_)
        | Ty::Fun(_, _)
        | Ty::FunNamedArgs(_, _)
        | Ty::AssocTySelect { .. } => (ty, false),
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
