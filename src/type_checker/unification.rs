use crate::ast;
use crate::collections::{Map, Set};
use crate::type_checker::loc_string;
use crate::type_checker::ty::*;

pub(super) fn unify(ty1: &Ty, ty2: &Ty, cons: &Map<Id, TyCon>, loc: &ast::Loc) {
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
                    "Unable to unify types {} and {} at {}",
                    con1,
                    con2,
                    loc_string(loc)
                )
            }
        }

        (Ty::App(con1, args1), Ty::App(con2, args2)) => {
            if con1 != con2 {
                panic!(
                    "Unable to unify types {} and {} at {}",
                    con1,
                    con2,
                    loc_string(loc)
                )
            }

            match (args1, args2) {
                (TyArgs::Positional(args1), TyArgs::Positional(args2)) => {
                    if args1.len() != args2.len() {
                        panic!("{}: BUG: Kind error: type constructor {} applied to different number of arguments in unify", loc_string(loc), con1)
                    }
                    for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                        unify(arg1, arg2, cons, loc);
                    }
                }
                (TyArgs::Named(args1), TyArgs::Named(args2)) => {
                    let keys1: Set<&Id> = args1.keys().collect();
                    let keys2: Set<&Id> = args2.keys().collect();
                    if keys1 != keys2 {
                        panic!("{}: BUG: Kind error: type constructor {} applied to different named arguments in unify", loc_string(loc), con1)
                    }

                    for key in keys1 {
                        unify(args1.get(key).unwrap(), args2.get(key).unwrap(), cons, loc);
                    }
                }
                _ => {
                    // Bug in the type checker, types should've been checked.
                    panic!("{}: BUG: Kind error: type constructor {} applied to different shape of arguments in unify", loc_string(loc), con1)
                }
            }
        }

        (Ty::QVar(var), _) | (_, Ty::QVar(var)) => {
            panic!("{}: QVar {} during unification", loc_string(loc), var);
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

        (Ty::Record(fields1), Ty::Record(fields2)) => {
            let keys1: Set<&Id> = fields1.keys().collect();
            let keys2: Set<&Id> = fields2.keys().collect();

            let extras1: Set<&&Id> = keys1.difference(&keys2).collect();
            let extras2: Set<&&Id> = keys2.difference(&keys1).collect();

            if !extras1.is_empty() {
                panic!(
                    "{}: Unable to unify records: extra keys: {:?}",
                    loc_string(loc),
                    extras1
                );
            }

            if !extras2.is_empty() {
                panic!(
                    "{}: Unable to unify records: extra keys: {:?}",
                    loc_string(loc),
                    extras2
                );
            }

            if keys1 != keys2 {
                panic!(
                    "{}: Unable to unify records: keys don't match",
                    loc_string(loc)
                );
            }

            for key in keys1 {
                let ty1 = fields1.get(key).unwrap();
                let ty2 = fields2.get(key).unwrap();
                unify(ty1, ty2, cons, loc);
            }
        }

        (ty1, ty2) => panic!(
            "Unable to unify types {:?} and {:?} at {}",
            ty1,
            ty2,
            loc_string(loc)
        ),
    }
}

/// When we have an expected type during type inference (i.e. we're in 'checking' mode), this
/// unifies the expected type with the inferred type, and returns one of the types.
pub(super) fn unify_expected_ty(
    ty: Ty,
    expected_ty: Option<&Ty>,
    cons: &Map<Id, TyCon>,
    loc: &ast::Loc,
) -> Ty {
    if let Some(expected_ty) = expected_ty {
        unify(&ty, expected_ty, cons, loc);
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
            assert!(var.link().is_none());
            var.prune_level(max_level);
        }

        Ty::App(_, tys) => match tys {
            TyArgs::Positional(tys) => tys.iter().for_each(|ty| prune_level(ty, max_level)),
            TyArgs::Named(tys) => tys.values().for_each(|ty| prune_level(ty, max_level)),
        },

        Ty::Record(fields) => {
            for field_ty in fields.values() {
                prune_level(field_ty, max_level);
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
