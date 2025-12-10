use crate::ast::{self, Id};
use crate::collections::*;
use crate::type_checker::loc_display;
use crate::type_checker::row_utils::*;
use crate::type_checker::ty::*;

pub(super) fn unify(
    ty1: &Ty,
    ty2: &Ty,
    cons: &ScopeMap<Id, TyCon>,
    var_gen: &mut TyVarGen,
    level: u32,
    loc: &ast::Loc,
) {
    let ty1 = ty1.normalize(cons);
    if ty1.is_void() {
        return;
    }

    let ty2 = ty2.normalize(cons);
    if ty2.is_void() {
        return;
    }

    match (&ty1, &ty2) {
        (Ty::Con(con1, _kind1), Ty::Con(con2, _kind2)) => {
            if con1 != con2 {
                panic!(
                    "{}: Unable to unify types {} and {}",
                    loc_display(loc),
                    con1,
                    con2,
                )
            }
        }

        (Ty::App(con1, args1, _kind1), Ty::App(con2, args2, _kind2)) => {
            if con1 != con2 {
                panic!(
                    "{}: Unable to unify types {} and {}",
                    loc_display(loc),
                    con1,
                    con2,
                )
            }
            if args1.len() != args2.len() {
                panic!(
                    "{}: BUG: Kind error: type constructor {} applied to different number of arguments in unify",
                    loc_display(loc),
                    con1
                )
            }
            for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                unify(arg1, arg2, cons, var_gen, level, loc);
            }
        }

        (
            Ty::Fun {
                args: args1,
                ret: ret1,
                exceptions: exceptions1,
            },
            Ty::Fun {
                args: args2,
                ret: ret2,
                exceptions: exceptions2,
            },
        ) => {
            if args1.len() != args2.len() {
                panic!(
                    "{}: Unable to unify functions {} and {} (argument numbers don't match)",
                    loc_display(loc),
                    ty1,
                    ty2
                );
            }

            match (args1, args2) {
                (FunArgs::Positional(args1), FunArgs::Positional(args2)) => {
                    for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                        unify(arg1, arg2, cons, var_gen, level, loc);
                    }
                }

                (FunArgs::Named(args1), FunArgs::Named(args2)) => {
                    let arg_names_1: Set<&Id> = args1.keys().collect();
                    let arg_names_2: Set<&Id> = args2.keys().collect();
                    if arg_names_1 != arg_names_2 {
                        panic!(
                            "{}: Unable to unify functions with different named arguments",
                            loc_display(loc)
                        );
                    }

                    for arg_name in arg_names_1 {
                        unify(
                            args1.get(arg_name).unwrap(),
                            args2.get(arg_name).unwrap(),
                            cons,
                            var_gen,
                            level,
                            loc,
                        );
                    }
                }

                (FunArgs::Named(_), FunArgs::Positional(_))
                | (FunArgs::Positional(_), FunArgs::Named(_)) => {
                    panic!(
                        "{}: Unable to unify functions with positional and named arguments",
                        loc_display(loc)
                    )
                }
            }

            match (exceptions1, exceptions2) {
                (None, None) => {}

                (None, Some(_)) | (Some(_), None) => {
                    // None is the same as [..r] with a fresh r, so it unifies with everything.
                }

                (Some(exceptions1), Some(exceptions2)) => {
                    unify(exceptions1, exceptions2, cons, var_gen, level, loc);
                }
            }

            unify(ret1, ret2, cons, var_gen, level, loc);
        }

        (Ty::QVar(var, _kind), _) | (_, Ty::QVar(var, _kind)) => {
            panic!("{}: QVar {} during unification", loc_display(loc), var);
        }

        (Ty::Var(var1), Ty::Var(var2)) => {
            if var1.id() == var2.id() {
                return;
            }

            let var1_level = var1.level();
            let var2_level = var2.level();

            // We've normalized the types, so the links must be followed to the end.
            debug_assert!(var1.link().is_none());
            debug_assert!(var2.link().is_none());

            // Links must increase in level so that we can follow them to find the level of the
            // group.
            if var1_level < var2_level {
                link_var(var1, &ty2);
            } else {
                link_var(var2, &ty1);
            }
        }

        (Ty::Var(var), ty2) => {
            if var.kind() != ty2.kind() {
                panic!(
                    "{}: Unable to unify var with kind {} with type with kind {}",
                    loc_display(loc),
                    var.kind(),
                    ty2.kind(),
                );
            }
            link_var(var, ty2)
        }

        (ty1, Ty::Var(var)) => {
            if var.kind() != ty1.kind() {
                panic!(
                    "{}: Unable to unify var with kind {} with type with kind {}",
                    loc_display(loc),
                    var.kind(),
                    ty1.kind(),
                );
            }
            link_var(var, ty1)
        }

        (
            Ty::Anonymous {
                labels: labels1,
                extension: extension1,
                kind: kind1,
                is_row: is_row_1,
            },
            Ty::Anonymous {
                labels: labels2,
                extension: extension2,
                kind: kind2,
                is_row: is_row_2,
            },
        ) => {
            // Kind mismatches can happen when try to unify a record with a variant (e.g. pass a
            // record when a variant is expected), and fail. Similary we can pass `row[]` when `[]`
            // is expected (or the other way around).
            if kind1 != kind2 || is_row_1 != is_row_2 {
                panic!(
                    "{}: Unable to unify {} {} with {} {}",
                    loc_display(loc),
                    kind1,
                    ty1,
                    kind2,
                    ty2,
                );
            }

            let (labels1, mut extension1) =
                collect_rows(cons, &ty1, *kind1, labels1, extension1.clone());
            let (labels2, mut extension2) =
                collect_rows(cons, &ty2, *kind2, labels2, extension2.clone());

            let keys1: Set<&Id> = labels1.keys().collect();
            let keys2: Set<&Id> = labels2.keys().collect();

            // Extra labels in one type will be added to the extension of the other.
            let extras1: Set<&&Id> = keys1.difference(&keys2).collect();
            let extras2: Set<&&Id> = keys2.difference(&keys1).collect();

            // Unify common labels.
            for key in keys1.intersection(&keys2) {
                let ty1 = labels1.get(*key).unwrap();
                let ty2 = labels2.get(*key).unwrap();
                unify(ty1, ty2, cons, var_gen, level, loc);
            }

            let (kind_str, label_str) = match kind1 {
                RecordOrVariant::Record => ("record", "field"),
                RecordOrVariant::Variant => ("variant", "constructor"),
            };

            if !extras1.is_empty() {
                match &extension2 {
                    Some(Ty::Var(var)) => {
                        // TODO: Not sure about level
                        extension2 = Some(Ty::Var(link_extension(
                            *kind2, &extras1, &labels1, var, var_gen, level, loc,
                        )));
                    }
                    _ => {
                        panic!(
                            "{}: Unable to unify {} with {}s {:?} with {} with {}s {:?}",
                            loc_display(loc),
                            kind_str,
                            label_str,
                            keys1,
                            kind_str,
                            label_str,
                            keys2
                        );
                    }
                }
            }

            if !extras2.is_empty() {
                match &extension1 {
                    Some(Ty::Var(var)) => {
                        // TODO: Not sure about level
                        extension1 = Some(Ty::Var(link_extension(
                            *kind1, &extras2, &labels2, var, var_gen, level, loc,
                        )));
                    }
                    _ => {
                        panic!(
                            "{}: Unable to unify {} with {}s {:?} with {} with {}s {:?}",
                            loc_display(loc),
                            kind_str,
                            label_str,
                            keys1,
                            kind_str,
                            label_str,
                            keys2
                        );
                    }
                }
            }

            fn unit_row(kind: RecordOrVariant) -> Ty {
                Ty::Anonymous {
                    labels: Default::default(),
                    extension: None,
                    kind,
                    is_row: true,
                }
            }

            match (extension1, extension2) {
                (None, None) => {}
                (Some(ext1), None) => {
                    unify(&ext1, &unit_row(*kind1), cons, var_gen, level, loc);
                }
                (None, Some(ext2)) => {
                    unify(&unit_row(*kind2), &ext2, cons, var_gen, level, loc);
                }
                (Some(ext1), Some(ext2)) => {
                    unify(&ext1, &ext2, cons, var_gen, level, loc);
                }
            }
        }

        (ty1, ty2) => panic!(
            "{}: Unable to unify types
             {} and
             {}
             (
                {:?}
                {:?}
             )",
            loc_display(loc),
            ty1,
            ty2,
            ty1,
            ty2,
        ),
    }
}

/// Try to unify `ty1` with the `ty2`, without updating `ty2`.
///
/// This does not panic on errors. Returns whether unification was successful.
pub(super) fn try_unify_one_way(
    ty1: &Ty,
    ty2: &Ty,
    cons: &ScopeMap<Id, TyCon>,
    var_gen: &mut TyVarGen,
    level: u32,
    loc: &ast::Loc,
) -> bool {
    let ty1 = ty1.normalize(cons);
    let ty2 = ty2.normalize(cons);
    match (&ty1, &ty2) {
        (Ty::Con(con1, _kind1), Ty::Con(con2, _kind2)) => con1 == con2,

        (Ty::App(con1, args1, _kind1), Ty::App(con2, args2, _kind2)) => {
            if con1 != con2 {
                return false;
            }
            if args1.len() != args2.len() {
                return false;
            }
            for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                if !try_unify_one_way(arg1, arg2, cons, var_gen, level, loc) {
                    return false;
                }
            }
            true
        }

        (
            Ty::Fun {
                args: args1,
                ret: ret1,
                exceptions: exceptions1,
            },
            Ty::Fun {
                args: args2,
                ret: ret2,
                exceptions: exceptions2,
            },
        ) => {
            if args1.len() != args2.len() {
                return false;
            }

            match (args1, args2) {
                (FunArgs::Positional(args1), FunArgs::Positional(args2)) => {
                    for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                        if !try_unify_one_way(arg1, arg2, cons, var_gen, level, loc) {
                            return false;
                        }
                    }
                }

                (FunArgs::Named(args1), FunArgs::Named(args2)) => {
                    let arg_names_1: Set<&Id> = args1.keys().collect();
                    let arg_names_2: Set<&Id> = args2.keys().collect();
                    if arg_names_1 != arg_names_2 {
                        return false;
                    }

                    for arg_name in arg_names_1 {
                        if !try_unify_one_way(
                            args1.get(arg_name).unwrap(),
                            args2.get(arg_name).unwrap(),
                            cons,
                            var_gen,
                            level,
                            loc,
                        ) {
                            return false;
                        }
                    }
                }

                (FunArgs::Named(_), FunArgs::Positional(_))
                | (FunArgs::Positional(_), FunArgs::Named(_)) => return false,
            }

            match (exceptions1, exceptions2) {
                (None, None) => {}

                (None, Some(_)) | (Some(_), None) => {
                    // None is the same as [..r] with a fresh r, so it unifies with everything.
                }

                (Some(exceptions1), Some(exceptions2)) => {
                    if !try_unify_one_way(exceptions1, exceptions2, cons, var_gen, level, loc) {
                        return false;
                    }
                }
            }

            try_unify_one_way(ret1, ret2, cons, var_gen, level, loc)
        }

        (Ty::QVar(var, _kind), _) | (_, Ty::QVar(var, _kind)) => {
            panic!("{}: QVar {} during unification", loc_display(loc), var);
        }

        (Ty::Var(var1), Ty::Var(var2)) => {
            if var1 == var2 {
                return true;
            }
            if var1.level() > var2.level() {
                var1.set_link(ty2);
            } else {
                var2.set_link(ty1);
            }
            true
        }

        (Ty::Var(var), ty2) => {
            link_var(var, ty2);
            true
        }

        (
            Ty::Anonymous {
                labels: labels1,
                extension: extension1,
                kind: kind1,
                is_row: is_row_1,
            },
            Ty::Anonymous {
                labels: labels2,
                extension: extension2,
                kind: kind2,
                is_row: is_row_2,
            },
        ) => {
            // Kind mismatches can happen when try to unify a record with a variant (e.g. pass a
            // record when a variant is expected), and fail.
            if kind1 != kind2 {
                return false;
            }

            // If we checked the kinds in type applications properly, we should only try to unify
            // rows with rows and stars with stars.
            assert_eq!(is_row_1, is_row_2);

            let (labels1, mut extension1) =
                collect_rows(cons, &ty1, *kind1, labels1, extension1.clone());
            let (labels2, extension2) =
                collect_rows(cons, &ty2, *kind2, labels2, extension2.clone());

            let keys1: Set<&Id> = labels1.keys().collect();
            let keys2: Set<&Id> = labels2.keys().collect();

            // Extra labels in one type will be added to the extension of the other.
            let extras1: Set<&&Id> = keys1.difference(&keys2).collect();
            let extras2: Set<&&Id> = keys2.difference(&keys1).collect();

            // Unify common labels.
            for key in keys1.intersection(&keys2) {
                let ty1 = labels1.get(*key).unwrap();
                let ty2 = labels2.get(*key).unwrap();
                if !try_unify_one_way(ty1, ty2, cons, var_gen, level, loc) {
                    return false;
                }
            }

            if !extras1.is_empty() {
                return false;
            }

            if !extras2.is_empty() {
                match &extension1 {
                    Some(Ty::Var(var)) => {
                        // TODO: Not sure about level
                        extension1 = Some(Ty::Var(link_extension(
                            *kind1, &extras2, &labels2, var, var_gen, level, loc,
                        )));
                    }
                    _ => {
                        return false;
                    }
                }
            }

            fn unit_row(kind: RecordOrVariant) -> Ty {
                Ty::Anonymous {
                    labels: Default::default(),
                    extension: None,
                    kind,
                    is_row: true,
                }
            }

            match (extension1, extension2) {
                (None, None) => true,
                (Some(ext1), None) => {
                    try_unify_one_way(&ext1, &unit_row(*kind1), cons, var_gen, level, loc)
                }
                (None, Some(_)) => false,
                (Some(ext1), Some(ext2)) => {
                    try_unify_one_way(&ext1, &ext2, cons, var_gen, level, loc)
                }
            }
        }

        (_, _) => false,
    }
}

fn link_extension(
    kind: RecordOrVariant,
    extra_labels: &Set<&&Id>,
    label_values: &TreeMap<Id, Ty>,
    var: &TyVarRef,
    var_gen: &mut TyVarGen,
    level: u32,
    loc: &ast::Loc,
) -> TyVarRef {
    let extension_labels: TreeMap<Id, Ty> = extra_labels
        .iter()
        .map(|extra_field| {
            (
                (**extra_field).clone(),
                label_values.get(**extra_field).unwrap().clone(),
            )
        })
        .collect();
    // TODO: Not sure about the level.
    let new_extension_var = var_gen.new_var(level, Kind::Row(kind), loc.clone());
    let new_extension_ty = Ty::Anonymous {
        labels: extension_labels,
        extension: Some(Box::new(Ty::Var(new_extension_var.clone()))),
        kind,
        is_row: true,
    };
    var.set_link(new_extension_ty);
    new_extension_var
}

/// When we have an expected type during type inference (i.e. we're in 'checking' mode), this
/// unifies the expected type with the inferred type, and returns one of the types.
pub(super) fn unify_expected_ty(
    ty: Ty,
    expected_ty: Option<&Ty>,
    cons: &ScopeMap<Id, TyCon>,
    var_gen: &mut TyVarGen,
    level: u32,
    loc: &ast::Loc,
) -> Ty {
    if let Some(expected_ty) = expected_ty {
        unify(&ty, expected_ty, cons, var_gen, level, loc);
    }
    ty
}

fn link_var(var: &TyVarRef, ty: &Ty) {
    // TODO: Occurs check.
    prune_level(ty, var.level());
    var.set_link(ty.clone());
}

fn prune_level(ty: &Ty, max_level: u32) {
    match ty {
        Ty::Con(_, _) => {}

        Ty::Var(var) => {
            // Assertion disabled for now, see #22.
            // assert!(var.link().is_none());
            var.prune_level(max_level);
        }

        Ty::App(_, tys, _) => tys.iter().for_each(|ty| prune_level(ty, max_level)),

        Ty::Anonymous {
            labels, extension, ..
        } => {
            for label_ty in labels.values() {
                prune_level(label_ty, max_level);
            }
            if let Some(ext) = extension {
                prune_level(ext, max_level);
            }
        }

        Ty::QVar(_, _) => panic!("QVar in prune_level"),

        Ty::Fun {
            args,
            ret,
            exceptions,
        } => {
            match args {
                FunArgs::Positional(args) => {
                    args.iter().for_each(|arg| prune_level(arg, max_level))
                }
                FunArgs::Named(args) => args.values().for_each(|arg| prune_level(arg, max_level)),
            }
            prune_level(ret, max_level);
            if let Some(exn) = exceptions {
                prune_level(exn, max_level);
            }
        }
    }
}
