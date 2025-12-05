use crate::ast::{self, Id, Loc};
use crate::collections::{Map, Set};
use crate::type_checker::{FunArgs, TcFunState, Ty, TyMap, row_utils};

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

/*
Before creating the matrix:

- Flatten all or patterns
- Sort all named fields
- Add all missing fields as underscore patterns

Note that these can be done lazily, as we create the next matrix from the current matrix + the
constructor to focus on.

Example:

match f():
    (a = Option.Some(123), b = Point(x = 0, y = 0)): ...
    (a = Option.None, ..): ...
    other: ...

==>

match f():
    (Option.Some(123), Point(0, 0)): ...
    (Option.None, _): ...
    (_, _): ...

Then create the matrix:

fields = Vec.[
    Vec.[`Option.Some(123)`, `Point(0, 0)`],
    Vec.[`Option.None`, _],
    Vec.[_, _],
]

ty = [Option[U32], Point]

For all values of the first field, all values of the rest of the fields should be fully covered.

Values of the first field: `Option.Some(...)` and `Option.None`. Focus on `Option.None`:

fields = Vec.[
    Vec.[_],
    Vec.[_],
]

ty = [Point]

Covered fully by the first pattern.

Focus on `Option.Some`:

fields = Vec.[
    Vec.[`123`, `Point(0, 0)`],
    Vec.[_, _],
]

ty = [U32, Point]

The first pattern cannot fully cover `U32` (only `_` can).

In the second pattern, we check that all of the rest of the patterns are fully covered. Matrix:

fields = Vec.[
    Vec.[_],
]

ty = [Point]

---

The type below implements the matrix + the focus operations.
*/
#[derive(Debug)]
pub(crate) struct PatMatrix {
    rows: Vec<Vec<ast::L<ast::Pat>>>,
    field_tys: Vec<Ty>,
}

impl PatMatrix {
    pub(crate) fn from_match_arms(arms: &[ast::Alt], scrut_ty: &Ty) -> PatMatrix {
        let mut rows: Vec<Vec<ast::L<ast::Pat>>> = Vec::with_capacity(arms.len());
        for arm in arms {
            if arm.guard.is_some() {
                continue;
            }
            rows.push(vec![arm.pattern.clone()]);
        }
        PatMatrix {
            rows,
            field_tys: vec![scrut_ty.clone()],
        }
    }

    // Entry point here.
    //
    // The scrutinee type should be deeply normalized. *I think* (but I'm not sure) we also want to
    // check all pattern types before calling this, to do the unifications before analyzing
    // scrutinee type deeply.
    //
    // We can't check RHSs before checking coverage though, because binder types will be refined
    // based on coverage.
    pub(crate) fn check_coverage(&self, tc_state: &TcFunState, loc: &ast::Loc) -> bool {
        // dbg!(self);

        let next_ty = match self.field_tys.get(0) {
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
                self.focus_wildcard().check_coverage(tc_state, loc)
            }

            Ty::Con(field_ty_con_id, _) | Ty::App(field_ty_con_id, _, _) => {
                // TODO: This doesn't handle: integers, strings, characters
                let field_con_details = tc_state
                    .tys
                    .tys
                    .get_con(&field_ty_con_id)
                    .unwrap()
                    .con_details()
                    .unwrap();

                // Check that every constructor of `next_ty` is covered.
                for con in field_con_details.cons.iter() {
                    let con_name = con
                        .name
                        .clone()
                        .unwrap_or_else(|| panic!("{}", crate::utils::loc_display(loc)));
                    // println!("  Checking con {}", con_name);
                    let matrix = self.focus_con(&field_ty_con_id, &con_name, tc_state);
                    if matrix.rows.is_empty() || !matrix.check_coverage(tc_state, loc) {
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
                    &labels,
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
                    let ty_matrix = PatMatrix {
                        rows: self.rows.clone(),
                        field_tys: ty_field_tys,
                    };
                    if !ty_matrix.check_coverage(tc_state, loc) {
                        return false;
                    }
                }

                // If variant can have more things, we need a wildcard at this position.
                if extension.is_some() {
                    if !self.focus_wildcard().check_coverage(tc_state, loc) {
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

                let (labels, extension) = row_utils::collect_rows(
                    tc_state.tys.tys.cons(),
                    &next_ty,
                    RecordOrVariant::Variant,
                    &labels,
                    extension.clone(),
                );

                let mut labels_vec: Vec<(SmolStr, Ty)> = labels.into_iter().collect();
                labels_vec.sort_by_key(|(key, _)| key.clone());

                let mut new_rows: Vec<Vec<ast::L<ast::Pat>>> = vec![];

                // Add the current column's fields.
                for row in self.rows.iter() {
                    let mut work: Vec<ast::L<ast::Pat>> = vec![row[0].clone()];
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

                                        for arg in pat_fields.iter() {
                                            let arg_name = arg.name.as_ref().unwrap();
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
                                        pat_fields
                                            .iter()
                                            .map(|named_field| named_field.node.clone())
                                            .chain(
                                                (0..labels_vec.len() - pat_fields.len())
                                                    .map(|_| ast::L::new_dummy(ast::Pat::Ignore)),
                                            )
                                            .collect()
                                    };

                                fields_positional.extend(row[1..].iter().cloned());

                                new_rows.push(fields_positional);
                            }

                            ast::Pat::Or(pat1, pat2) => {
                                work.push((*pat1).clone());
                                work.push((*pat2).clone());
                            }

                            ast::Pat::Var(_) | ast::Pat::Ignore => {}

                            ast::Pat::Constr(_) | ast::Pat::Str(_) | ast::Pat::Char(_) => {
                                // type error
                                panic!();
                            }
                        }
                    }
                }

                let mut new_field_tys: Vec<Ty> =
                    labels_vec.iter().map(|(_name, ty)| ty.clone()).collect();
                new_field_tys.extend(self.field_tys.iter().skip(1).cloned());

                PatMatrix {
                    rows: new_rows,
                    field_tys: new_field_tys,
                }
                .check_coverage(tc_state, loc)
            }

            Ty::Var(_) | Ty::QVar(_, _) | Ty::Fun { .. } => {
                self.focus_wildcard().check_coverage(tc_state, loc)
            }
        }
    }

    fn num_fields(&self) -> usize {
        self.field_tys.len()
    }

    fn focus_con(&self, con_ty_id: &Id, con_id: &Id, tc_state: &TcFunState) -> PatMatrix {
        assert!(self.num_fields() > 0);

        let (field_ty_con_id, field_ty_con_ty_args) =
            self.field_tys[0].con(tc_state.tys.tys.cons()).unwrap();
        assert_eq!(con_ty_id, &field_ty_con_id);

        // Get constructor field types from the constructor's type scheme.
        let con_scheme = tc_state
            .tys
            .associated_fn_schemes
            .get(con_ty_id)
            .unwrap()
            .get(con_id)
            .unwrap();

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

        let args_positional: Vec<Ty> = match &args {
            FunArgs::Positional(args) => args.clone(),
            FunArgs::Named(named_args) => {
                let mut args_vec: Vec<(&Id, &Ty)> = named_args.iter().collect();
                args_vec.sort_by_key(|(id, _)| *id);
                args_vec.into_iter().map(|(_, ty)| ty.clone()).collect()
            }
        };

        let mut new_rows: Vec<Vec<ast::L<ast::Pat>>> = vec![];

        // Add the current column's fields.
        for row in self.rows.iter() {
            let mut work: Vec<ast::L<ast::Pat>> = vec![row[0].clone()];
            while let Some(pat) = work.pop() {
                match pat.node {
                    ast::Pat::Constr(ast::ConstrPattern {
                        constr: ast::Constructor { ty, constr, .. },
                        fields,
                        ignore_rest: _,
                    }) => {
                        // Note: `ty` may not be the same as `con_ty_id` when checking variant
                        // patterns. We need to compare both type and constructor names.
                        if !(ty == *con_ty_id && Some(con_id) == constr.as_ref()) {
                            continue;
                        }

                        let mut fields_positional: Vec<ast::L<ast::Pat>> = if !fields.is_empty()
                            && fields[0].name.is_some()
                        {
                            let mut fields_vec: Vec<(Id, ast::L<ast::Pat>)> = fields
                                .iter()
                                .map(|named_field| {
                                    (named_field.name.clone().unwrap(), named_field.node.clone())
                                })
                                .collect();

                            // The pattern may be missing some of the fields in the constructor.
                            // Add ignore pats for those.
                            let field_pat_names: Set<&Id> = fields
                                .iter()
                                .map(|field| field.name.as_ref().unwrap())
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

                        fields_positional.extend(row[1..].iter().cloned());

                        new_rows.push(fields_positional);
                    }

                    ast::Pat::Record(_) => todo!(),

                    ast::Pat::Var(_) | ast::Pat::Ignore => {
                        // All fields are fully covered.
                        let fields_positional: Vec<ast::L<ast::Pat>> =
                            std::iter::repeat_with(|| ast::L::new_dummy(ast::Pat::Ignore))
                                .take(args_positional.len())
                                .collect();
                        new_rows.push(fields_positional);
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

        PatMatrix {
            rows: new_rows,
            field_tys: new_field_tys,
        }
    }

    fn focus_wildcard(&self) -> PatMatrix {
        let mut new_rows: Vec<Vec<ast::L<ast::Pat>>> = vec![];

        for row in self.rows.iter() {
            if matches!(row[0].node, ast::Pat::Var(_) | ast::Pat::Ignore) {
                new_rows.push(row.iter().skip(1).cloned().collect());
            }
        }

        let new_field_tys: Vec<Ty> = self.field_tys.iter().skip(1).cloned().collect();

        PatMatrix {
            rows: new_rows,
            field_tys: new_field_tys,
        }
    }
}
