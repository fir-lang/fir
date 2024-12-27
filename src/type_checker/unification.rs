use crate::ast::{self, Id};
use crate::collections::{Map, ScopeMap, Set};
use crate::type_checker::loc_display;
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
        (Ty::Con(con1), Ty::Con(con2)) => {
            if con1 != con2 {
                panic!(
                    "{}: Unable to unify types {} and {}",
                    loc_display(loc),
                    con1,
                    con2,
                )
            }
        }

        (Ty::App(con1, args1), Ty::App(con2, args2)) => {
            if con1 != con2 {
                panic!(
                    "{}: Unable to unify types {} and {}",
                    loc_display(loc),
                    con1,
                    con2,
                )
            }

            match (args1, args2) {
                (TyArgs::Positional(args1), TyArgs::Positional(args2)) => {
                    if args1.len() != args2.len() {
                        panic!("{}: BUG: Kind error: type constructor {} applied to different number of arguments in unify", loc_display(loc), con1)
                    }
                    for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                        unify(arg1, arg2, cons, var_gen, level, loc);
                    }
                }
                (TyArgs::Named(args1), TyArgs::Named(args2)) => {
                    let keys1: Set<&Id> = args1.keys().collect();
                    let keys2: Set<&Id> = args2.keys().collect();
                    if keys1 != keys2 {
                        panic!("{}: BUG: Kind error: type constructor {} applied to different named arguments in unify", loc_display(loc), con1)
                    }

                    for key in keys1 {
                        unify(
                            args1.get(key).unwrap(),
                            args2.get(key).unwrap(),
                            cons,
                            var_gen,
                            level,
                            loc,
                        );
                    }
                }
                _ => {
                    // Bug in the type checker, types should've been checked.
                    panic!("{}: BUG: Kind error: type constructor {} applied to different shape of arguments in unify", loc_display(loc), con1)
                }
            }
        }

        (Ty::Fun(args1, ret1), Ty::Fun(args2, ret2)) => {
            if args1.len() != args2.len() {
                panic!(
                    "{}: Unable to unify functions {} and {} (argument numbers)",
                    loc_display(loc),
                    ty1,
                    ty2
                );
            }

            for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                unify(arg1, arg2, cons, var_gen, level, loc);
            }

            unify(ret1, ret2, cons, var_gen, level, loc);
        }

        (Ty::QVar(var), _) | (_, Ty::QVar(var)) => {
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

        (Ty::Var(var), ty2) => link_var(var, ty2),

        (ty1, Ty::Var(var)) => link_var(var, ty1),

        (
            Ty::Record {
                fields: fields1,
                extension: extension1,
            },
            Ty::Record {
                fields: fields2,
                extension: extension2,
            },
        ) => {
            let (record1_fields, record1_extension) =
                collect_record_fields(cons, &ty1, fields1, extension1.clone());
            let (record2_fields, record2_extension) =
                collect_record_fields(cons, &ty2, fields2, extension2.clone());
            let make_concrete = record1_extension.is_none() || record2_extension.is_none();

            let keys1: Set<&Id> = record1_fields.keys().collect();
            let keys2: Set<&Id> = record2_fields.keys().collect();

            // Extra fields in one record will be added to the extension of the other.
            let extras1: Set<&&Id> = keys1.difference(&keys2).collect();
            let extras2: Set<&&Id> = keys2.difference(&keys1).collect();

            // Unify common fields.
            for key in keys1.intersection(&keys2) {
                let ty1 = record1_fields.get(*key).unwrap();
                let ty2 = record2_fields.get(*key).unwrap();
                unify(ty1, ty2, cons, var_gen, level, loc);
            }

            if !extras1.is_empty() {
                match &record2_extension {
                    Some(Ty::Var(var)) => {
                        // TODO: Not sure about level
                        link_record_extension(
                            &extras1,
                            &record1_fields,
                            &var,
                            var_gen,
                            level,
                            !make_concrete,
                            loc,
                        );
                    }
                    _ => {
                        panic!(
                            "{}: Unable to unify records: extra keys: {:?}",
                            loc_display(loc),
                            extras1
                        );
                    }
                }
            }

            if !extras2.is_empty() {
                match &record1_extension {
                    Some(Ty::Var(var)) => {
                        // TODO: Not sure about level
                        link_record_extension(
                            &extras2,
                            &record2_fields,
                            &var,
                            var_gen,
                            level,
                            !make_concrete,
                            loc,
                        );
                    }
                    _ => {
                        panic!(
                            "{}: Unable to unify records: extra keys: {:?}",
                            loc_display(loc),
                            extras2
                        );
                    }
                }
            }

            if extras1.is_empty() && extras2.is_empty() && make_concrete {
                if let Some(extension) = &record1_extension {
                    unify(extension, &Ty::unit(), cons, var_gen, level, loc);
                }
                if let Some(extension) = &record2_extension {
                    unify(extension, &Ty::unit(), cons, var_gen, level, loc);
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

/// Returns all of the fields in the record including extensions, with extension variable (if
/// exists).
pub(crate) fn collect_record_fields<'a>(
    cons: &ScopeMap<Id, TyCon>,
    record_ty: &Ty, // used in errors
    fields: &Map<Id, Ty>,
    mut extension: Option<Box<Ty>>,
) -> (Map<Id, Ty>, Option<Ty>) {
    let mut all_fields: Map<Id, Ty> = fields
        .iter()
        .map(|(id, ty)| (id.clone(), ty.clone()))
        .collect();

    while let Some(ext) = extension {
        match *ext {
            Ty::Record {
                fields,
                extension: next_ext,
            } => {
                for (field_id, field_ty) in fields {
                    if all_fields.insert(field_id, field_ty).is_some() {
                        panic!("Duplicate field in record {}", record_ty);
                    }
                }
                extension = next_ext;
            }

            Ty::Var(var) => match var.normalize(cons) {
                Ty::Record {
                    fields,
                    extension: next_ext,
                } => {
                    for (field_id, field_ty) in fields {
                        if all_fields.insert(field_id, field_ty).is_some() {
                            panic!("Duplicate field in record {}", record_ty);
                        }
                    }
                    extension = next_ext;
                }

                other => return (all_fields, Some(other)),
            },

            other => return (all_fields, Some(other)),
        }
    }

    (all_fields, None)
}

fn link_record_extension(
    extra_fields: &Set<&&Id>,
    field_values: &Map<Id, Ty>,
    var: &TyVarRef,
    var_gen: &mut TyVarGen,
    level: u32,
    generate_new_extension: bool,
    loc: &ast::Loc,
) {
    let extension_fields: Map<Id, Ty> = extra_fields
        .iter()
        .map(|extra_field| {
            (
                (**extra_field).clone(),
                field_values.get(**extra_field).unwrap().clone(),
            )
        })
        .collect();
    let new_extension_var = if generate_new_extension {
        // TODO: Not sure about the level.
        Some(Box::new(Ty::Var(var_gen.new_var(level, loc.clone()))))
    } else {
        None
    };
    let new_extension_ty = Ty::Record {
        fields: extension_fields,
        extension: new_extension_var,
    };
    var.set_link(new_extension_ty);
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
        Ty::Con(_) => {}

        Ty::Var(var) => {
            // Assertion disabled for now, see #22.
            // assert!(var.link().is_none());
            var.prune_level(max_level);
        }

        Ty::App(_, tys) => match tys {
            TyArgs::Positional(tys) => tys.iter().for_each(|ty| prune_level(ty, max_level)),
            TyArgs::Named(tys) => tys.values().for_each(|ty| prune_level(ty, max_level)),
        },

        Ty::Record { fields, extension } => {
            for field_ty in fields.values() {
                prune_level(field_ty, max_level);
            }
            if let Some(ext) = extension {
                prune_level(ext, max_level);
            }
        }

        Ty::QVar(_) => panic!("QVar in prune_level"),

        Ty::Fun(args, ret) => {
            for arg in args {
                prune_level(arg, max_level);
            }
            prune_level(ret, max_level);
        }

        Ty::FunNamedArgs(args, ret) => {
            for arg in args.values() {
                prune_level(arg, max_level);
            }
            prune_level(ret, max_level);
        }

        Ty::AssocTySelect { ty, assoc_ty: _ } => {
            prune_level(ty, max_level);
        }
    }
}
