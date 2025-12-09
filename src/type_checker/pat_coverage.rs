use crate::ast::{self, Id, Loc};
use crate::collections::{Map, Set};
use crate::type_checker::{FunArgs, Scheme, TcFunState, Ty, TyMap, row_utils};
#[allow(unused)]
use crate::utils::loc_display;

use super::RecordOrVariant;

use smol_str::SmolStr;

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

            ast::Pat::Str(_) | ast::Pat::Char(_) => {}
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

////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone)]
pub(crate) struct PatMatrix {
    rows: Vec<Row>,
    field_tys: Vec<Ty>,
}

#[derive(Debug, Clone)]
struct Row {
    /// `match` arm index the row is generated from.
    arm_index: ArmIndex,
    pats: Vec<ast::L<ast::Pat>>,
}

type ArmIndex = u32;

impl Row {
    fn len(&self) -> usize {
        self.pats.len()
    }
}

impl std::fmt::Display for PatMatrix {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        for row_idx in 0..self.rows.len() {
            if row_idx != 0 {
                writeln!(f)?;
                write!(f, " ")?;
            }
            let row = &self.rows[row_idx];
            write!(f, "arm{}=[", row.arm_index)?;
            assert_eq!(row.len(), self.field_tys.len());
            for (field_idx, pat) in row.pats.iter().enumerate() {
                if field_idx != 0 {
                    write!(f, ", ")?;
                }
                let field_ty = &self.field_tys[field_idx];
                write!(f, "{}:{}", pat.node, field_ty)?;
            }
            write!(f, "]")?;
        }
        write!(f, "]")
    }
}

impl PatMatrix {
    pub(crate) fn from_match_arms(arms: &[ast::Alt], scrut_ty: &Ty) -> PatMatrix {
        let mut rows: Vec<Row> = Vec::with_capacity(arms.len());
        for (arm_index, arm) in arms.iter().enumerate() {
            if arm.guard.is_some() {
                // TODO: Alternatives with guards can't add to coverage, but their binders still
                // need refinement.
                continue;
            }
            rows.push(Row {
                arm_index: arm_index as u32,
                pats: vec![arm.pattern.clone()],
            });
        }
        PatMatrix::new(rows, vec![scrut_ty.clone()])
    }

    fn new(rows: Vec<Row>, field_tys: Vec<Ty>) -> PatMatrix {
        if cfg!(debug_assertions) {
            for row in rows.iter() {
                assert_eq!(row.len(), field_tys.len());
            }
        }
        PatMatrix { rows, field_tys }
    }

    fn skip_col(&self) -> PatMatrix {
        PatMatrix {
            rows: self
                .rows
                .iter()
                .map(|row| Row {
                    arm_index: row.arm_index,
                    pats: row.pats.iter().skip(1).cloned().collect(),
                })
                .collect(),
            field_tys: self.field_tys.iter().skip(1).cloned().collect(),
        }
    }

    // Entry point here.
    #[allow(clippy::only_used_in_recursion)]
    pub(crate) fn check_coverage(
        &self,
        tc_state: &TcFunState,
        loc: &ast::Loc,
        trace: &mut Vec<String>,
    ) -> bool {
        // dbg!(self);

        // if !trace.is_empty() {
        //     println!();
        // }
        // print!("{}", indent(&trace.join(", "), trace.len() * 4));
        // print!("{}", indent(&self.to_string(), trace.len() * 4));

        if self.field_tys.is_empty() {
            return true;
        }

        // If all of the rows have a wildcard as the next pattern, skip the column to avoid
        // recursing when the type being matched is recursive.
        let all_wildcards = self.rows.iter().all(|row| {
            matches!(
                row.pats.first().as_ref().unwrap().node,
                ast::Pat::Var(_) | ast::Pat::Ignore
            )
        });

        if all_wildcards {
            return with_trace(trace, "_".to_string(), |trace| {
                self.skip_col().check_coverage(tc_state, loc, trace)
            });
        }

        let next_ty = match self.field_tys.first() {
            Some(next_ty) => next_ty.deep_normalize(tc_state.tys.tys.cons()),
            None => return true,
        };

        match &next_ty {
            Ty::Con(field_ty_con_id, _) | Ty::App(field_ty_con_id, _, _)
                if field_ty_con_id == &SmolStr::new_static("Str")
                    || field_ty_con_id == &SmolStr::new_static("Char")
                    || field_ty_con_id == &SmolStr::new_static("U8")
                    || field_ty_con_id == &SmolStr::new_static("I8")
                    || field_ty_con_id == &SmolStr::new_static("U16")
                    || field_ty_con_id == &SmolStr::new_static("I16")
                    || field_ty_con_id == &SmolStr::new_static("U32")
                    || field_ty_con_id == &SmolStr::new_static("I32")
                    || field_ty_con_id == &SmolStr::new_static("U64")
                    || field_ty_con_id == &SmolStr::new_static("I64") =>
            {
                with_trace(trace, field_ty_con_id.to_string(), |trace| {
                    self.focus_wildcard().check_coverage(tc_state, loc, trace)
                })
            }

            Ty::Con(field_ty_con_id, _) | Ty::App(field_ty_con_id, _, _) => {
                // TODO: This doesn't handle: integers, strings, characters
                let field_con_details = tc_state
                    .tys
                    .tys
                    .get_con(field_ty_con_id)
                    .unwrap()
                    .con_details()
                    .unwrap();

                // Check that every constructor of `next_ty` is covered.
                for con in field_con_details.cons.iter() {
                    let matrix = match &con.name {
                        Some(con_name) => {
                            self.focus_sum_con(field_ty_con_id, con_name, tc_state, loc)
                        }
                        None => self.focus_product_con(field_ty_con_id, tc_state, loc),
                    };
                    let s = match &con.name {
                        Some(con) => format!("{}.{}", field_ty_con_id, con),
                        None => field_ty_con_id.to_string(),
                    };
                    if matrix.rows.is_empty()
                        || !with_trace(trace, s, |trace| {
                            matrix.check_coverage(tc_state, loc, trace)
                        })
                    {
                        return false;
                    }
                }

                true
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
                    &next_ty,
                    RecordOrVariant::Variant,
                    labels,
                    extension.clone(),
                );

                // Check coverage of each of the types in the variant, in the current matrix.
                for ty in labels.values() {
                    // This is a bit hacky and slow, we can refactor this later.
                    // We want to check the current matrix with a given current type, and a list of
                    // types (field_tys) for the rest of the field types.
                    let mut ty_field_tys: Vec<Ty> = Vec::with_capacity(self.field_tys.len());
                    ty_field_tys.push(ty.clone());
                    ty_field_tys.extend(self.field_tys.iter().skip(1).cloned());
                    let ty_matrix = PatMatrix::new(self.rows.clone(), ty_field_tys);
                    if !with_trace(trace, ty.to_string(), |trace| {
                        ty_matrix.check_coverage(tc_state, loc, trace)
                    }) {
                        return false;
                    }
                }

                // If variant can have more things, we need a wildcard at this position.
                if extension.is_some()
                    && !with_trace(trace, "extra rows".to_string(), |trace| {
                        self.focus_wildcard().check_coverage(tc_state, loc, trace)
                    })
                {
                    return false;
                }

                true
            }

            Ty::Anonymous {
                labels,
                extension,
                kind: RecordOrVariant::Record,
                is_row,
            } => {
                // Note: the code below is basically `focus_record`. We should probably move it to
                // its own function.
                //
                // There's some duplication in here and `focus_con`, but also lots of small
                // different parts. Not sure if we should have a function used by both.

                assert!(!is_row);

                // Row extensions don't matter for exhaustiveness as extra fields are not matched.
                let (labels, _extension) = row_utils::collect_rows(
                    tc_state.tys.tys.cons(),
                    &next_ty,
                    RecordOrVariant::Record,
                    labels,
                    extension.clone(),
                );

                let mut labels_vec: Vec<(SmolStr, Ty)> = labels.into_iter().collect();
                labels_vec.sort_by_key(|(key, _)| key.clone());

                let mut new_rows: Vec<Row> = vec![];

                // Add the current column's fields.
                for row in self.rows.iter() {
                    let mut work: Vec<ast::L<ast::Pat>> = vec![row.pats[0].clone()];
                    while let Some(pat) = work.pop() {
                        match pat.node {
                            ast::Pat::Record(ast::RecordPattern {
                                fields: pat_fields,
                                ignore_rest: _,
                                ..
                            }) => {
                                let mut fields_positional: Vec<ast::L<ast::Pat>> =
                                    if !pat_fields.is_empty() && pat_fields[0].name.is_some() {
                                        let mut fields_vec: Vec<(Id, ast::L<ast::Pat>)> =
                                            pat_fields
                                                .iter()
                                                .map(|named_field| {
                                                    (
                                                        named_field.name.clone().unwrap(),
                                                        named_field.node.clone(),
                                                    )
                                                })
                                                .collect();

                                        // The pattern may be missing some of the fields in the constructor.
                                        // Add ignore pats for those.
                                        let field_pat_names: Set<&Id> = pat_fields
                                            .iter()
                                            .map(|field| field.name.as_ref().unwrap())
                                            .collect();

                                        for (label, _) in labels_vec.iter() {
                                            if !field_pat_names.contains(label) {
                                                fields_vec.push((
                                                    label.clone(),
                                                    ast::L::new_dummy(ast::Pat::Ignore),
                                                ));
                                            }
                                        }

                                        fields_vec.sort_by_key(|(id, _)| id.clone());
                                        fields_vec.into_iter().map(|(_, pat)| pat).collect()
                                    } else {
                                        pat_fields
                                            .iter()
                                            .map(|named_field| named_field.node.clone())
                                            .chain(
                                                (0..labels_vec.len() - pat_fields.len())
                                                    .map(|_| ast::L::new_dummy(ast::Pat::Ignore)),
                                            )
                                            .collect()
                                    };

                                fields_positional.extend(row.pats[1..].iter().cloned());

                                new_rows.push(Row {
                                    arm_index: row.arm_index,
                                    pats: fields_positional,
                                });
                            }

                            ast::Pat::Or(pat1, pat2) => {
                                work.push((*pat1).clone());
                                work.push((*pat2).clone());
                            }

                            ast::Pat::Var(_) | ast::Pat::Ignore => {
                                let mut fields_positional: Vec<ast::L<ast::Pat>> = vec![];
                                for _ in labels_vec.iter() {
                                    fields_positional.push(ast::L::new_dummy(ast::Pat::Ignore));
                                }
                                fields_positional.extend(row.pats[1..].iter().cloned());
                                new_rows.push(Row {
                                    arm_index: row.arm_index,
                                    pats: fields_positional,
                                });
                            }

                            ast::Pat::Constr(_) | ast::Pat::Str(_) | ast::Pat::Char(_) => {
                                // type error
                                panic!();
                            }
                        } // match pat
                    } // pats in the row
                } // rows

                let mut new_field_tys: Vec<Ty> =
                    labels_vec.iter().map(|(_name, ty)| ty.clone()).collect();
                new_field_tys.extend(self.field_tys.iter().skip(1).cloned());

                with_trace(trace, "flattened".to_string(), |trace| {
                    PatMatrix::new(new_rows, new_field_tys).check_coverage(tc_state, loc, trace)
                })
            }

            Ty::Var(_) | Ty::QVar(_, _) | Ty::Fun { .. } => {
                with_trace(trace, "wildcard".to_string(), |trace| {
                    self.focus_wildcard().check_coverage(tc_state, loc, trace)
                })
            }
        }
    }

    fn num_fields(&self) -> usize {
        self.field_tys.len()
    }

    fn focus_product_con(
        &self,
        con_ty_id: &Id,
        tc_state: &TcFunState,
        loc: &ast::Loc,
    ) -> PatMatrix {
        assert!(self.num_fields() > 0);
        let con_scheme = tc_state.tys.top_schemes.get(con_ty_id).unwrap();
        self.focus_con_scheme(con_ty_id, None, con_scheme, tc_state, loc)
    }

    fn focus_sum_con(
        &self,
        con_ty_id: &Id,
        con_id: &Id,
        tc_state: &TcFunState,
        loc: &ast::Loc,
    ) -> PatMatrix {
        // println!("focus {}.{}", con_ty_id, con_id);

        assert!(self.num_fields() > 0);

        // Get constructor field types from the constructor's type scheme.
        let con_scheme = tc_state
            .tys
            .associated_fn_schemes
            .get(con_ty_id)
            .unwrap()
            .get(con_id)
            .unwrap();

        self.focus_con_scheme(con_ty_id, Some(con_id), con_scheme, tc_state, loc)
    }

    fn focus_con_scheme(
        &self,
        con_ty_id: &Id,
        con_id: Option<&Id>,
        con_scheme: &Scheme,
        tc_state: &TcFunState,
        #[allow(unused)] loc: &ast::Loc,
    ) -> PatMatrix {
        let (field_ty_con_id, field_ty_con_ty_args) =
            self.field_tys[0].con(tc_state.tys.tys.cons()).unwrap();
        assert_eq!(con_ty_id, &field_ty_con_id);

        let mut preds = vec![];

        let con_fn_ty =
            con_scheme.instantiate_with_tys(&field_ty_con_ty_args, &mut preds, &ast::Loc::dummy());

        // Constructors can't have predicates.
        assert!(preds.is_empty());

        let (args, _): (FunArgs, Ty) = match con_fn_ty {
            Ty::Fun {
                args,
                ret,
                exceptions,
            } => {
                // Constructors don't have exception types.
                assert!(exceptions.is_none());
                (args, *ret)
            }

            other => (FunArgs::empty(), other),
        };

        // println!("con_ty_id = {}, con_id = {:?}, args = {:?}", con_ty_id, con_id, args);

        let named_args;

        let args_positional: Vec<Ty> = match &args {
            FunArgs::Positional(args) => {
                named_args = false;
                args.clone()
            }
            FunArgs::Named(args) => {
                named_args = true;
                let mut args_vec: Vec<(&Id, &Ty)> = args.iter().collect();
                args_vec.sort_by_key(|(id, _)| *id);
                args_vec.into_iter().map(|(_, ty)| ty.clone()).collect()
            }
        };

        let mut new_rows: Vec<Row> = vec![];

        // Add the current column's fields.
        for row in self.rows.iter() {
            // assert!(!row.is_empty(), "empty row at {}", loc_display(loc));
            let mut work: Vec<ast::L<ast::Pat>> = vec![row.pats[0].clone()];
            while let Some(pat) = work.pop() {
                match pat.node {
                    ast::Pat::Constr(ast::ConstrPattern {
                        constr: ast::Constructor { ty, constr, .. },
                        fields,
                        ignore_rest: _,
                    }) => {
                        // Note: `ty` may not be the same as `con_ty_id` when checking variant
                        // patterns. We need to compare both type and constructor names.
                        if !(ty == *con_ty_id && con_id == constr.as_ref()) {
                            continue;
                        }

                        // The pattern may be missing some of the fields in the constructor.
                        // Add ignore pats for those.
                        let mut field_pat_names: Set<&Id> = Default::default();

                        let mut fields_positional: Vec<ast::L<ast::Pat>> = if named_args {
                            let mut fields_vec: Vec<(Id, ast::L<ast::Pat>)> = fields
                                .iter()
                                .map(|named_field| {
                                    let name = match &named_field.name {
                                        Some(name) => name,
                                        None => {
                                            // Con takes named params, but pat has positional. The
                                            // pat should be variable with the same name as the
                                            // field. (type checker checks this)
                                            match &named_field.node.node {
                                                ast::Pat::Var(ast::VarPat { var, ty: _ }) => var,
                                                _ => panic!(),
                                            }
                                        }
                                    };
                                    let new = field_pat_names.insert(name);
                                    assert!(new);
                                    (name.clone(), named_field.node.clone())
                                })
                                .collect();

                            for (arg_name, _) in args.as_named().iter() {
                                if !field_pat_names.contains(arg_name) {
                                    fields_vec.push((
                                        arg_name.clone(),
                                        ast::L::new_dummy(ast::Pat::Ignore),
                                    ));
                                }
                            }

                            fields_vec.sort_by_key(|(id, _)| id.clone());
                            fields_vec.into_iter().map(|(_, pat)| pat).collect()
                        } else {
                            fields
                                .iter()
                                .map(|named_field| named_field.node.clone())
                                .chain(
                                    (0..args_positional.len() - fields.len())
                                        .map(|_| ast::L::new_dummy(ast::Pat::Ignore)),
                                )
                                .collect()
                        };

                        fields_positional.extend(row.pats[1..].iter().cloned());

                        new_rows.push(Row {
                            arm_index: row.arm_index,
                            pats: fields_positional,
                        });
                    }

                    ast::Pat::Record(_) => todo!(),

                    ast::Pat::Var(_) | ast::Pat::Ignore => {
                        // All fields are fully covered.
                        let mut fields_positional: Vec<ast::L<ast::Pat>> =
                            std::iter::repeat_with(|| ast::L::new_dummy(ast::Pat::Ignore))
                                .take(args_positional.len())
                                .collect();
                        fields_positional.extend(row.pats[1..].iter().cloned());
                        new_rows.push(Row {
                            arm_index: row.arm_index,
                            pats: fields_positional,
                        });
                    }

                    ast::Pat::Str(_) | ast::Pat::Char(_) => {
                        // Not necessarily a type error or bug (in the type checker), we may be
                        // checking a variant.
                    }

                    ast::Pat::Or(pat1, pat2) => {
                        work.push((*pat1).clone());
                        work.push((*pat2).clone());
                    }
                }
            }
        }

        let mut new_field_tys: Vec<Ty> = args_positional;
        new_field_tys.extend(self.field_tys.iter().skip(1).cloned());

        PatMatrix::new(new_rows, new_field_tys)
    }

    fn focus_wildcard(&self) -> PatMatrix {
        let mut new_rows: Vec<Row> = vec![];

        for row in self.rows.iter() {
            if matches!(row.pats[0].node, ast::Pat::Var(_) | ast::Pat::Ignore) {
                new_rows.push(Row {
                    arm_index: row.arm_index,
                    pats: row.pats.iter().skip(1).cloned().collect(),
                });
            }
        }

        let new_field_tys: Vec<Ty> = self.field_tys.iter().skip(1).cloned().collect();

        PatMatrix::new(new_rows, new_field_tys)
    }
}

#[allow(unused)]
fn indent(s: &str, indent: usize) -> String {
    let mut ret = String::new();
    for line in s.lines() {
        for _ in 0..indent {
            ret.push(' ');
        }
        ret.push_str(line);
        ret.push('\n');
    }
    ret
}

#[allow(unused)]
fn with_trace<T, F: FnOnce(&mut Vec<String>) -> T>(trace: &mut Vec<String>, s: String, cb: F) -> T {
    trace.push(s);
    let ret = cb(trace);
    trace.pop();
    ret
}
