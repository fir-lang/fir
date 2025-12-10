use crate::ast::{self, Id};
use crate::collections::{Map, Set};
use crate::type_checker::{FunArgs, Scheme, TcFunState, Ty, row_utils};
#[allow(unused)]
use crate::utils::loc_display;

use super::RecordOrVariant;

use smol_str::SmolStr;

// Entry point.
pub(crate) fn check_coverage(
    arms: &[ast::Alt],
    scrut_ty: &Ty,
    tc_state: &TcFunState,
    loc: &ast::Loc,
) -> (bool, CoverageInfo) {
    let mut info = CoverageInfo::from_match_arms(arms);
    let exhaustive = PatMatrix::from_match_arms(arms, scrut_ty).check_coverage(
        tc_state,
        loc,
        &mut info,
        &mut Vec::with_capacity(10),
    );
    (exhaustive, info)
}

/// Invariants:
///
/// - There will be at least one row.
/// - Number of columns in the rows will be the same as number of field types.
///
/// These invariants are checked in `PatMatrix::new`. `PatMatrix::new_opt` returns `None` when there
/// are no rows.
#[derive(Debug, Clone)]
struct PatMatrix {
    rows: Vec<Row>,
    field_tys: Vec<Ty>,
}

#[derive(Debug, Clone)]
struct Row {
    /// `match` arm index the row is generated from.
    arm_index: ArmIndex,
    pats: Vec<ast::L<ast::Pat>>,
    bound_vars: Map<Id, Set<Ty>>,
    guarded: bool,
}

#[derive(Debug, Clone)]
pub(crate) struct CoverageInfo {
    /// Maps arm indices to variables bound in the arms.
    pub(crate) bound_vars: Vec<Map<Id, Set<Ty>>>,

    /// Maps arm indices to whether its useful.
    pub(crate) usefulness: Vec<bool>,
}

impl CoverageInfo {
    fn from_match_arms(arms: &[ast::Alt]) -> Self {
        CoverageInfo {
            bound_vars: vec![Default::default(); arms.len()],
            usefulness: vec![false; arms.len()],
        }
    }

    fn mark_useful(&mut self, arm_idx: ArmIndex, bound_vars: &Map<Id, Set<Ty>>) {
        for (var, tys) in bound_vars.iter() {
            self.bound_vars[arm_idx as usize]
                .entry(var.clone())
                .or_default()
                .extend(tys.iter().cloned());
        }

        self.usefulness[arm_idx as usize] = true;
    }

    pub(crate) fn is_useful(&self, arm_idx: ArmIndex) -> bool {
        self.usefulness[arm_idx as usize]
    }
}

type ArmIndex = u32;

impl Row {
    fn len(&self) -> usize {
        self.pats.len()
    }

    fn bind(&mut self, var: Id, ty: Ty) {
        self.bound_vars.entry(var).or_default().insert(ty);
    }
}

impl PatMatrix {
    fn from_match_arms(arms: &[ast::Alt], scrut_ty: &Ty) -> PatMatrix {
        let mut rows: Vec<Row> = Vec::with_capacity(arms.len());
        for (arm_index, arm) in arms.iter().enumerate() {
            rows.push(Row {
                arm_index: arm_index as u32,
                pats: vec![arm.pattern.clone()],
                bound_vars: Default::default(),
                guarded: arm.guard.is_some(),
            });
        }
        PatMatrix::new(rows, vec![scrut_ty.clone()])
    }

    fn new(rows: Vec<Row>, field_tys: Vec<Ty>) -> PatMatrix {
        assert!(!rows.is_empty());
        if cfg!(debug_assertions) {
            for row in rows.iter() {
                assert_eq!(row.len(), field_tys.len());
            }
        }
        PatMatrix { rows, field_tys }
    }

    fn new_opt(rows: Vec<Row>, field_tys: Vec<Ty>) -> Option<PatMatrix> {
        if rows.is_empty() {
            None
        } else {
            Some(PatMatrix::new(rows, field_tys))
        }
    }

    // Entry point here.
    #[allow(clippy::only_used_in_recursion)]
    fn check_coverage(
        &self,
        tc_state: &TcFunState,
        loc: &ast::Loc,
        info: &mut CoverageInfo,
        trace: &mut Vec<String>,
    ) -> bool {
        // if !trace.is_empty() {
        //     println!();
        // }
        // print!("{}", indent(&trace.join(", "), trace.len() * 4));
        // print!("{}", indent(&self.to_string(), trace.len() * 4));

        let next_ty = match self.field_tys.first() {
            Some(next_ty) => next_ty.deep_normalize(tc_state.tys.tys.cons()),
            None => {
                for row in self.rows.iter() {
                    info.mark_useful(row.arm_index, &row.bound_vars);
                    if !row.guarded {
                        break;
                    }
                }
                // There should be at least one non-guarded arm.
                return self.rows.iter().any(|row| !row.guarded);
            }
        };

        // If all of the rows have a wildcard as the next pattern, skip the column to avoid
        // recursing when the type being matched is recursive.
        if let Some(matrix) = self.skip_col(&next_ty) {
            return with_trace(trace, "_".to_string(), |trace| {
                matrix.check_coverage(tc_state, loc, info, trace)
            });
        }

        match &next_ty {
            Ty::Con(field_ty_con_id, _) | Ty::App(field_ty_con_id, _, _) => {
                let field_con_details = tc_state
                    .tys
                    .tys
                    .get_con(field_ty_con_id)
                    .unwrap()
                    .con_details()
                    .unwrap();

                let mut exhaustive = true;

                // Check that every constructor of `next_ty` is covered.
                for con in field_con_details.cons.iter() {
                    let matrix = match &con.name {
                        Some(con_name) => {
                            self.focus_sum_con(&next_ty, field_ty_con_id, con_name, tc_state, loc)
                        }
                        None => self.focus_product_con(&next_ty, field_ty_con_id, tc_state, loc),
                    };
                    let s = match &con.name {
                        Some(con) => format!("{}.{}", field_ty_con_id, con),
                        None => field_ty_con_id.to_string(),
                    };
                    match matrix {
                        Some(matrix) => {
                            if !with_trace(trace, s, |trace| {
                                matrix.check_coverage(tc_state, loc, info, trace)
                            }) {
                                // This constructor is handled, but the rest of the fields are not.
                                exhaustive = false;
                            }
                        }
                        None => {
                            // Constructor is not handled.
                            exhaustive = false;
                        }
                    }
                }

                exhaustive
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

                let mut exhaustive = true;

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
                        ty_matrix.check_coverage(tc_state, loc, info, trace)
                    }) {
                        exhaustive = false;
                    }
                }

                // If variant can have more things, we need a wildcard at this position.
                if let Some(extension) = &extension {
                    match self.skip_wildcards(&Ty::Anonymous {
                        labels: Default::default(),
                        extension: Some(Box::new(extension.clone())),
                        kind: RecordOrVariant::Variant,
                        is_row: false,
                    }) {
                        Some(skipped) => {
                            if !with_trace(trace, "extra rows".to_string(), |trace| {
                                skipped.check_coverage(tc_state, loc, info, trace)
                            }) {
                                exhaustive = false;
                            }
                        }
                        None => exhaustive = false,
                    }
                }

                exhaustive
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
                                    bound_vars: row.bound_vars.clone(),
                                    guarded: row.guarded,
                                });
                            } // ast::Pat::Record

                            ast::Pat::Or(pat1, pat2) => {
                                work.push((*pat1).clone());
                                work.push((*pat2).clone());
                            }

                            ast::Pat::Var(var) => {
                                let mut fields_positional: Vec<ast::L<ast::Pat>> = vec![];
                                for _ in labels_vec.iter() {
                                    fields_positional.push(ast::L::new_dummy(ast::Pat::Ignore));
                                }
                                fields_positional.extend(row.pats[1..].iter().cloned());
                                let mut row = Row {
                                    arm_index: row.arm_index,
                                    pats: fields_positional,
                                    bound_vars: row.bound_vars.clone(),
                                    guarded: row.guarded,
                                };
                                row.bind(var.var.clone(), next_ty.clone());
                                new_rows.push(row);
                            }

                            ast::Pat::Ignore => {
                                let mut fields_positional: Vec<ast::L<ast::Pat>> = vec![];
                                for _ in labels_vec.iter() {
                                    fields_positional.push(ast::L::new_dummy(ast::Pat::Ignore));
                                }
                                fields_positional.extend(row.pats[1..].iter().cloned());
                                new_rows.push(Row {
                                    arm_index: row.arm_index,
                                    pats: fields_positional,
                                    bound_vars: row.bound_vars.clone(),
                                    guarded: row.guarded,
                                });
                            }

                            ast::Pat::Constr(_) | ast::Pat::Str(_) | ast::Pat::Char(_) => {
                                // type error
                                panic!();
                            }

                            ast::Pat::Variant(_) => {
                                todo!()
                            }
                        } // match pat
                    } // pats in the row
                } // rows

                let mut new_field_tys: Vec<Ty> =
                    labels_vec.iter().map(|(_name, ty)| ty.clone()).collect();
                new_field_tys.extend(self.field_tys.iter().skip(1).cloned());

                with_trace(trace, "flattened".to_string(), |trace| {
                    PatMatrix::new(new_rows, new_field_tys)
                        .check_coverage(tc_state, loc, info, trace)
                })
            } // Ty::Anonymous(kind: Record)

            Ty::Var(_) | Ty::QVar(_, _) | Ty::Fun { .. } => match self.skip_wildcards(&next_ty) {
                Some(skipped) => with_trace(trace, "wildcard".to_string(), |trace| {
                    skipped.check_coverage(tc_state, loc, info, trace)
                }),
                None => false,
            },
        }
    }

    fn num_fields(&self) -> usize {
        self.field_tys.len()
    }

    fn focus_product_con(
        &self,
        ty: &Ty,
        con_ty_id: &Id,
        tc_state: &TcFunState,
        loc: &ast::Loc,
    ) -> Option<PatMatrix> {
        assert!(self.num_fields() > 0);
        let con_scheme = tc_state.tys.top_schemes.get(con_ty_id).unwrap();
        self.focus_con_scheme(ty, con_ty_id, None, con_scheme, tc_state, loc)
    }

    fn focus_sum_con(
        &self,
        ty: &Ty,
        con_ty_id: &Id,
        con_id: &Id,
        tc_state: &TcFunState,
        loc: &ast::Loc,
    ) -> Option<PatMatrix> {
        assert!(self.num_fields() > 0);

        // Get constructor field types from the constructor's type scheme.
        let con_scheme = tc_state
            .tys
            .associated_fn_schemes
            .get(con_ty_id)
            .unwrap()
            .get(con_id)
            .unwrap();

        self.focus_con_scheme(ty, con_ty_id, Some(con_id), con_scheme, tc_state, loc)
    }

    fn focus_con_scheme(
        &self,
        ty: &Ty,
        con_ty_id: &Id,
        con_id: Option<&Id>,
        con_scheme: &Scheme,
        tc_state: &TcFunState,
        #[allow(unused)] loc: &ast::Loc,
    ) -> Option<PatMatrix> {
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
                            bound_vars: row.bound_vars.clone(),
                            guarded: row.guarded,
                        });
                    }

                    ast::Pat::Var(var) => {
                        // All fields are fully covered.
                        let mut fields_positional: Vec<ast::L<ast::Pat>> =
                            std::iter::repeat_with(|| ast::L::new_dummy(ast::Pat::Ignore))
                                .take(args_positional.len())
                                .collect();
                        fields_positional.extend(row.pats[1..].iter().cloned());
                        let mut row = Row {
                            arm_index: row.arm_index,
                            pats: fields_positional,
                            bound_vars: row.bound_vars.clone(),
                            guarded: row.guarded,
                        };
                        row.bind(var.var.clone(), ty.clone());
                        new_rows.push(row);
                    }

                    ast::Pat::Ignore | ast::Pat::Record(_) => {
                        // All fields are fully covered.
                        let mut fields_positional: Vec<ast::L<ast::Pat>> =
                            std::iter::repeat_with(|| ast::L::new_dummy(ast::Pat::Ignore))
                                .take(args_positional.len())
                                .collect();
                        fields_positional.extend(row.pats[1..].iter().cloned());
                        new_rows.push(Row {
                            arm_index: row.arm_index,
                            pats: fields_positional,
                            bound_vars: row.bound_vars.clone(),
                            guarded: row.guarded,
                        });
                    }

                    ast::Pat::Str(_) | ast::Pat::Char(_) => {
                        // Not necessarily a type error or bug (in the type checker), we may be
                        // checking a variant.
                        let mut fields_positional: Vec<ast::L<ast::Pat>> =
                            std::iter::repeat_with(|| ast::L::new_dummy(ast::Pat::Ignore))
                                .take(args_positional.len())
                                .collect();
                        fields_positional.extend(row.pats[1..].iter().cloned());
                        new_rows.push(Row {
                            arm_index: row.arm_index,
                            pats: fields_positional,
                            bound_vars: row.bound_vars.clone(),
                            // Treat literal patterns as match-all with guards.
                            guarded: true,
                        });
                    }

                    ast::Pat::Or(pat1, pat2) => {
                        work.push((*pat1).clone());
                        work.push((*pat2).clone());
                    }

                    ast::Pat::Variant(_) => {
                        todo!()
                    }
                } // match pat
            } // pats in the row
        } // row

        let mut new_field_tys: Vec<Ty> = args_positional;
        new_field_tys.extend(self.field_tys.iter().skip(1).cloned());

        PatMatrix::new_opt(new_rows, new_field_tys)
    }

    /// Skip the current column in the matrix if all of the patterns in the column are wildcards.
    fn skip_col(&self, ty: &Ty) -> Option<PatMatrix> {
        if let Some(skipped) = self.skip_wildcards(ty)
            && skipped.rows.len() == self.rows.len()
        {
            Some(skipped)
        } else {
            None
        }
    }

    /// Filter rows with wildcard (variable or underscore) patterns and skip the column.
    ///
    /// This should be used when matching an abstract type (a type variable), or a type that can't
    /// be exhaustively matched (e.g. strings, integers), as those can only be matched with a
    /// wildcard pattern.
    ///
    /// `None` return value means there were no rows with a wildcard pattern on the first column, so
    /// we weren't able to really "skip".
    fn skip_wildcards(&self, ty: &Ty) -> Option<PatMatrix> {
        let mut new_rows: Vec<Row> = vec![];

        for row in self.rows.iter() {
            match &row.pats[0].node {
                ast::Pat::Var(var) => {
                    let mut row = Row {
                        arm_index: row.arm_index,
                        pats: row.pats.iter().skip(1).cloned().collect(),
                        bound_vars: row.bound_vars.clone(),
                        guarded: row.guarded,
                    };
                    row.bind(var.var.clone(), ty.clone());
                    new_rows.push(row);
                }

                ast::Pat::Ignore => {
                    new_rows.push(Row {
                        arm_index: row.arm_index,
                        pats: row.pats.iter().skip(1).cloned().collect(),
                        bound_vars: row.bound_vars.clone(),
                        guarded: row.guarded,
                    });
                }

                _ => {}
            }
        }

        let new_field_tys: Vec<Ty> = self.field_tys.iter().skip(1).cloned().collect();

        PatMatrix::new_opt(new_rows, new_field_tys)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Debug helpers

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
            write!(f, "] vars={}", BoundVarsDisplay(&row.bound_vars))?;
        }
        write!(f, "]")
    }
}

struct BoundVarsDisplay<'a>(&'a Map<Id, Set<Ty>>);

impl<'a> std::fmt::Display for BoundVarsDisplay<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for (var_idx, (var, tys)) in self.0.iter().enumerate() {
            if var_idx != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}: [", var)?;
            for (ty_idx, ty) in tys.iter().enumerate() {
                if ty_idx != 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", ty)?;
            }
            write!(f, "]")?;
        }
        write!(f, "}}")
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
