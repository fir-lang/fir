use crate::ast::{self, Name};
use crate::collections::*;
use crate::type_checker::id::Id;
use crate::type_checker::loc_display;
use crate::type_checker::row_utils::*;
use crate::type_checker::traits::TraitEnv;
use crate::type_checker::ty::*;

pub(super) fn unify(
    ty1: &Ty,
    ty2: &Ty,
    cons: &ScopeMap<Id, TyCon>,
    trait_env: &TraitEnv,
    var_gen: &UVarGen,
    loc: &ast::Loc,
    assumps: &[Pred],
    preds: &mut Vec<Pred>,
) {
    let ty1 = ty1.deep_normalize(cons, trait_env, var_gen, assumps);
    let ty2 = ty2.deep_normalize(cons, trait_env, var_gen, assumps);

    if ty1.kind() != ty2.kind() {
        panic!(
            "{}: Unable to unify types {} and {} (kind mismatch, {} ~ {})",
            loc_display(loc),
            ty1,
            ty2,
            ty1.kind(),
            ty2.kind(),
        )
    }

    match (&ty1, &ty2) {
        (Ty::Con(con1, _kind1), Ty::Con(con2, _kind2)) => {
            if con1 != con2 {
                panic!(
                    "{}: Unable to unify types {} and {}",
                    loc_display(loc),
                    con1.name(),
                    con2.name(),
                )
            }
        }

        (Ty::RVar(con1, _kind1), Ty::RVar(con2, _kind2)) => {
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
                    con1.name(),
                    con2.name(),
                )
            }
            if args1.len() != args2.len() {
                panic!(
                    "{}: BUG: Kind error: type constructor {} applied to different number of arguments in unify",
                    loc_display(loc),
                    con1.name()
                )
            }
            for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                unify(arg1, arg2, cons, trait_env, var_gen, loc, assumps, preds);
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
                (FunArgs::Positional { args: args1 }, FunArgs::Positional { args: args2 }) => {
                    for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                        unify(arg1, arg2, cons, trait_env, var_gen, loc, assumps, preds);
                    }
                }

                (
                    FunArgs::Named {
                        args: args1,
                        extension: extension1,
                    },
                    FunArgs::Named {
                        args: args2,
                        extension: extension2,
                    },
                ) => {
                    unify_record_labels(
                        &ty1, args1, extension1, &ty2, args2, extension2, cons, trait_env, var_gen,
                        loc, assumps, preds,
                    );
                }

                (FunArgs::Named { .. }, FunArgs::Positional { .. })
                | (FunArgs::Positional { .. }, FunArgs::Named { .. }) => {
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
                    unify(
                        exceptions1,
                        exceptions2,
                        cons,
                        trait_env,
                        var_gen,
                        loc,
                        assumps,
                        preds,
                    );
                }
            }

            unify(ret1, ret2, cons, trait_env, var_gen, loc, assumps, preds);
        }

        (Ty::QVar(var, _kind), _) | (_, Ty::QVar(var, _kind)) => {
            panic!("{}: QVar {} during unification", loc_display(loc), var);
        }

        (Ty::UVar(var1), Ty::UVar(var2)) => {
            if var1.id() == var2.id() {
                return;
            }

            // We've normalized the types, so the links must be followed to the end.
            debug_assert!(var1.link().is_none());
            debug_assert!(var2.link().is_none());

            // Arbitrary but deterministic linking direction.
            if var1.id() < var2.id() {
                link_var(var1, &ty2);
            } else {
                link_var(var2, &ty1);
            }
        }

        (Ty::UVar(var), ty2) => link_var(var, ty2),

        (ty1, Ty::UVar(var)) => link_var(var, ty1),

        (
            Ty::Record {
                labels: labels1,
                extension: extension1,
                is_row: _,
            },
            Ty::Record {
                labels: labels2,
                extension: extension2,
                is_row: _,
            },
        ) => {
            unify_record_labels(
                &ty1, labels1, extension1, &ty2, labels2, extension2, cons, trait_env, var_gen,
                loc, assumps, preds,
            );
        }

        (
            Ty::Variant {
                labels: labels1,
                extension: extension1,
                is_row: _,
            },
            Ty::Variant {
                labels: labels2,
                extension: extension2,
                is_row: _,
            },
        ) => {
            unify_variant_labels(
                &ty1, labels1, extension1, &ty2, labels2, extension2, cons, trait_env, var_gen,
                loc, assumps, preds,
            );
        }

        // Unify an empty anonymous row with another type. `row(..ext)` with no labels is just
        // `ext`, which should unify with anything as long as kinds match.
        (
            Ty::Record {
                labels,
                extension: Some(ext),
                is_row: true,
            },
            other,
        )
        | (
            other,
            Ty::Record {
                labels,
                extension: Some(ext),
                is_row: true,
            },
        ) if labels.is_empty() => {
            unify(ext, other, cons, trait_env, var_gen, loc, assumps, preds);
        }

        (
            Ty::Variant {
                labels,
                extension: Some(ext),
                is_row: true,
            },
            other,
        )
        | (
            other,
            Ty::Variant {
                labels,
                extension: Some(ext),
                is_row: true,
            },
        ) if labels.is_empty() => {
            unify(ext, other, cons, trait_env, var_gen, loc, assumps, preds);
        }

        (
            Ty::AssocTySelect {
                ty: ty1_inner,
                assoc_ty: assoc1,
                kind: _,
            },
            Ty::AssocTySelect {
                ty: ty2_inner,
                assoc_ty: assoc2,
                kind: _,
            },
        ) => {
            if assoc1 != assoc2 {
                panic!(
                    "{}: Unable to unify types {} and {}",
                    loc_display(loc),
                    ty1,
                    ty2,
                );
            }
            unify(
                ty1_inner, ty2_inner, cons, trait_env, var_gen, loc, assumps, preds,
            );
        }

        (
            Ty::AssocTySelect {
                ty: inner_ty,
                assoc_ty,
                kind: _,
            },
            other,
        )
        | (
            other,
            Ty::AssocTySelect {
                ty: inner_ty,
                assoc_ty,
                kind: _,
            },
        ) => {
            let (trait_id, trait_args): (&Id, &[Ty]) = match inner_ty.as_ref() {
                Ty::App(con, args, _) => (con, args.as_slice()),
                Ty::Con(con, _) => (con, &[]),
                _ => panic!(
                    "{}: Cannot construct predicate from AssocTySelect with inner type: {}",
                    loc_display(loc),
                    inner_ty,
                ),
            };
            preds.push(Pred {
                trait_: trait_id.clone(),
                params: trait_args.to_vec(),
                assoc_ty: Some((assoc_ty.clone(), other.clone())),
                loc: loc.clone(),
            });
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

#[allow(clippy::too_many_arguments)]
fn unify_record_labels(
    ty1: &Ty,
    labels1: &OrdMap<Name, Ty>,
    extension1: &Option<Box<Ty>>,
    ty2: &Ty,
    labels2: &OrdMap<Name, Ty>,
    extension2: &Option<Box<Ty>>,
    cons: &ScopeMap<Id, TyCon>,
    trait_env: &TraitEnv,
    var_gen: &UVarGen,
    loc: &ast::Loc,
    assumps: &[Pred],
    preds: &mut Vec<Pred>,
) {
    let (labels1, mut extension1) = collect_record_rows(
        cons,
        ty1,
        labels1,
        extension1.clone(),
        &Default::default(),
        var_gen,
        assumps,
    );
    let (labels2, mut extension2) = collect_record_rows(
        cons,
        ty2,
        labels2,
        extension2.clone(),
        &Default::default(),
        var_gen,
        assumps,
    );

    let keys1: HashSet<&Name> = labels1.keys().collect();
    let keys2: HashSet<&Name> = labels2.keys().collect();

    // Extra labels in one type will be added to the extension of the other.
    let extras1: HashSet<&&Name> = keys1.difference(&keys2).collect();
    let extras2: HashSet<&&Name> = keys2.difference(&keys1).collect();

    // Unify common labels.
    for key in keys1.intersection(&keys2) {
        let ty1 = labels1.get(*key).unwrap();
        let ty2 = labels2.get(*key).unwrap();
        unify(ty1, ty2, cons, trait_env, var_gen, loc, assumps, preds);
    }

    if !extras1.is_empty() {
        match &extension2 {
            Some(Ty::UVar(var)) => {
                extension2 = Some(Ty::UVar(link_record_extension(
                    &extras1, &labels1, var, var_gen, loc,
                )));
            }
            _ => {
                panic!("{}: Unable to unify {} with {}", loc_display(loc), ty1, ty2,);
            }
        }
    }

    if !extras2.is_empty() {
        match &extension1 {
            Some(Ty::UVar(var)) => {
                extension1 = Some(Ty::UVar(link_record_extension(
                    &extras2, &labels2, var, var_gen, loc,
                )));
            }
            _ => {
                panic!("{}: Unable to unify {} with {}", loc_display(loc), ty1, ty2,);
            }
        }
    }

    fn unit_row() -> Ty {
        Ty::Record {
            labels: Default::default(),
            extension: None,
            is_row: true,
        }
    }

    match (extension1, extension2) {
        (None, None) => {}
        (Some(ext1), None) => {
            unify(
                &ext1,
                &unit_row(),
                cons,
                trait_env,
                var_gen,
                loc,
                assumps,
                preds,
            );
        }
        (None, Some(ext2)) => {
            unify(
                &unit_row(),
                &ext2,
                cons,
                trait_env,
                var_gen,
                loc,
                assumps,
                preds,
            );
        }
        (Some(ext1), Some(ext2)) => {
            unify(&ext1, &ext2, cons, trait_env, var_gen, loc, assumps, preds);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn unify_variant_labels(
    ty1: &Ty,
    labels1: &OrdMap<Id, Ty>,
    extension1: &Option<Box<Ty>>,
    ty2: &Ty,
    labels2: &OrdMap<Id, Ty>,
    extension2: &Option<Box<Ty>>,
    cons: &ScopeMap<Id, TyCon>,
    trait_env: &TraitEnv,
    var_gen: &UVarGen,
    loc: &ast::Loc,
    assumps: &[Pred],
    preds: &mut Vec<Pred>,
) {
    let (labels1, mut extension1) = collect_variant_rows(
        cons,
        ty1,
        labels1,
        extension1.clone(),
        &Default::default(),
        var_gen,
        assumps,
    );
    let (labels2, mut extension2) = collect_variant_rows(
        cons,
        ty2,
        labels2,
        extension2.clone(),
        &Default::default(),
        var_gen,
        assumps,
    );

    let keys1: HashSet<&Id> = labels1.keys().collect();
    let keys2: HashSet<&Id> = labels2.keys().collect();

    let extras1: HashSet<&&Id> = keys1.difference(&keys2).collect();
    let extras2: HashSet<&&Id> = keys2.difference(&keys1).collect();

    for key in keys1.intersection(&keys2) {
        let ty1 = labels1.get(*key).unwrap();
        let ty2 = labels2.get(*key).unwrap();
        unify(ty1, ty2, cons, trait_env, var_gen, loc, assumps, preds);
    }

    if !extras1.is_empty() {
        match &extension2 {
            Some(Ty::UVar(var)) => {
                extension2 = Some(Ty::UVar(link_variant_extension(
                    &extras1, &labels1, var, var_gen, loc,
                )));
            }
            _ => {
                panic!("{}: Unable to unify {} with {}", loc_display(loc), ty1, ty2,);
            }
        }
    }

    if !extras2.is_empty() {
        match &extension1 {
            Some(Ty::UVar(var)) => {
                extension1 = Some(Ty::UVar(link_variant_extension(
                    &extras2, &labels2, var, var_gen, loc,
                )));
            }
            _ => {
                panic!("{}: Unable to unify {} with {}", loc_display(loc), ty1, ty2,);
            }
        }
    }

    fn unit_row() -> Ty {
        Ty::Variant {
            labels: Default::default(),
            extension: None,
            is_row: true,
        }
    }

    match (extension1, extension2) {
        (None, None) => {}
        (Some(ext1), None) => {
            unify(
                &ext1,
                &unit_row(),
                cons,
                trait_env,
                var_gen,
                loc,
                assumps,
                preds,
            );
        }
        (None, Some(ext2)) => {
            unify(
                &unit_row(),
                &ext2,
                cons,
                trait_env,
                var_gen,
                loc,
                assumps,
                preds,
            );
        }
        (Some(ext1), Some(ext2)) => {
            unify(&ext1, &ext2, cons, trait_env, var_gen, loc, assumps, preds);
        }
    }
}

/// Try to unify `ty1` with the `ty2`, without updating `ty2`.
///
/// This does not panic on errors. Returns whether unification was successful.
pub(super) fn try_unify_one_way(
    ty1: &Ty,
    ty2: &Ty,
    cons: &ScopeMap<Id, TyCon>,
    var_gen: &UVarGen,
    loc: &ast::Loc,
) -> bool {
    let ty1 = ty1.normalize(cons);
    let ty2 = ty2.normalize(cons);
    if ty1.kind() != ty2.kind() {
        return false;
    }
    match (&ty1, &ty2) {
        (Ty::Con(con1, _kind1), Ty::Con(con2, _kind2)) => con1 == con2,

        (Ty::RVar(con1, _kind1), Ty::RVar(con2, _kind2)) => con1 == con2,

        (Ty::App(con1, args1, _kind1), Ty::App(con2, args2, _kind2)) => {
            if con1 != con2 {
                return false;
            }
            if args1.len() != args2.len() {
                return false;
            }
            for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                if !try_unify_one_way(arg1, arg2, cons, var_gen, loc) {
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
                (FunArgs::Positional { args: args1 }, FunArgs::Positional { args: args2 }) => {
                    for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                        if !try_unify_one_way(arg1, arg2, cons, var_gen, loc) {
                            return false;
                        }
                    }
                }

                (
                    FunArgs::Named {
                        args: args1,
                        extension: extension1,
                    },
                    FunArgs::Named {
                        args: args2,
                        extension: extension2,
                    },
                ) => {
                    if !try_unify_record_labels_one_way(
                        &ty1, args1, extension1, &ty2, args2, extension2, cons, var_gen, loc,
                    ) {
                        return false;
                    }
                }

                (FunArgs::Named { .. }, FunArgs::Positional { .. })
                | (FunArgs::Positional { .. }, FunArgs::Named { .. }) => return false,
            }

            match (exceptions1, exceptions2) {
                (None, None) => {}

                (None, Some(_)) | (Some(_), None) => {
                    // None is the same as [..r] with a fresh r, so it unifies with everything.
                }

                (Some(exceptions1), Some(exceptions2)) => {
                    if !try_unify_one_way(exceptions1, exceptions2, cons, var_gen, loc) {
                        return false;
                    }
                }
            }

            try_unify_one_way(ret1, ret2, cons, var_gen, loc)
        }

        (Ty::QVar(var, _kind), _) | (_, Ty::QVar(var, _kind)) => {
            panic!("{}: QVar {} during unification", loc_display(loc), var);
        }

        (Ty::UVar(var1), Ty::UVar(var2)) => {
            if var1 == var2 {
                return true;
            }
            // Arbitrary but deterministic linking direction.
            if var1.id() < var2.id() {
                var1.set_link(ty2);
            } else {
                var2.set_link(ty1);
            }
            true
        }

        (Ty::UVar(var), ty2) => {
            link_var(var, ty2);
            true
        }

        (
            Ty::Record {
                labels: labels1,
                extension: extension1,
                is_row: _,
            },
            Ty::Record {
                labels: labels2,
                extension: extension2,
                is_row: _,
            },
        ) => try_unify_record_labels_one_way(
            &ty1, labels1, extension1, &ty2, labels2, extension2, cons, var_gen, loc,
        ),

        (
            Ty::Variant {
                labels: labels1,
                extension: extension1,
                is_row: _,
            },
            Ty::Variant {
                labels: labels2,
                extension: extension2,
                is_row: _,
            },
        ) => try_unify_variant_labels_one_way(
            &ty1, labels1, extension1, &ty2, labels2, extension2, cons, var_gen, loc,
        ),

        (
            Ty::AssocTySelect {
                ty: ty1_inner,
                assoc_ty: assoc1,
                kind: _,
            },
            Ty::AssocTySelect {
                ty: ty2_inner,
                assoc_ty: assoc2,
                kind: _,
            },
        ) => {
            if assoc1 != assoc2 {
                return false;
            }
            try_unify_one_way(ty1_inner, ty2_inner, cons, var_gen, loc)
        }

        (_, _) => false,
    }
}

#[allow(clippy::too_many_arguments)]
fn try_unify_record_labels_one_way(
    ty1: &Ty,
    labels1: &OrdMap<Name, Ty>,
    extension1: &Option<Box<Ty>>,
    ty2: &Ty,
    labels2: &OrdMap<Name, Ty>,
    extension2: &Option<Box<Ty>>,
    cons: &ScopeMap<Id, TyCon>,
    var_gen: &UVarGen,
    loc: &ast::Loc,
) -> bool {
    let (labels1, mut extension1) = collect_record_rows(
        cons,
        ty1,
        labels1,
        extension1.clone(),
        &Default::default(),
        var_gen,
        &[],
    );
    let (labels2, extension2) = collect_record_rows(
        cons,
        ty2,
        labels2,
        extension2.clone(),
        &Default::default(),
        var_gen,
        &[],
    );

    let keys1: HashSet<&Name> = labels1.keys().collect();
    let keys2: HashSet<&Name> = labels2.keys().collect();

    let extras1: HashSet<&&Name> = keys1.difference(&keys2).collect();
    let extras2: HashSet<&&Name> = keys2.difference(&keys1).collect();

    for key in keys1.intersection(&keys2) {
        let ty1 = labels1.get(*key).unwrap();
        let ty2 = labels2.get(*key).unwrap();
        if !try_unify_one_way(ty1, ty2, cons, var_gen, loc) {
            return false;
        }
    }

    if !extras1.is_empty() {
        return false;
    }

    if !extras2.is_empty() {
        match &extension1 {
            Some(Ty::UVar(var)) => {
                extension1 = Some(Ty::UVar(link_record_extension(
                    &extras2, &labels2, var, var_gen, loc,
                )));
            }
            _ => {
                return false;
            }
        }
    }

    fn unit_row() -> Ty {
        Ty::Record {
            labels: Default::default(),
            extension: None,
            is_row: true,
        }
    }

    match (extension1, extension2) {
        (None, None) => true,
        (Some(ext1), None) => try_unify_one_way(&ext1, &unit_row(), cons, var_gen, loc),
        (None, Some(_)) => false,
        (Some(ext1), Some(ext2)) => try_unify_one_way(&ext1, &ext2, cons, var_gen, loc),
    }
}

#[allow(clippy::too_many_arguments)]
fn try_unify_variant_labels_one_way(
    ty1: &Ty,
    labels1: &OrdMap<Id, Ty>,
    extension1: &Option<Box<Ty>>,
    ty2: &Ty,
    labels2: &OrdMap<Id, Ty>,
    extension2: &Option<Box<Ty>>,
    cons: &ScopeMap<Id, TyCon>,
    var_gen: &UVarGen,
    loc: &ast::Loc,
) -> bool {
    let (labels1, mut extension1) = collect_variant_rows(
        cons,
        ty1,
        labels1,
        extension1.clone(),
        &Default::default(),
        var_gen,
        &[],
    );
    let (labels2, extension2) = collect_variant_rows(
        cons,
        ty2,
        labels2,
        extension2.clone(),
        &Default::default(),
        var_gen,
        &[],
    );

    let keys1: HashSet<&Id> = labels1.keys().collect();
    let keys2: HashSet<&Id> = labels2.keys().collect();

    let extras1: HashSet<&&Id> = keys1.difference(&keys2).collect();
    let extras2: HashSet<&&Id> = keys2.difference(&keys1).collect();

    for key in keys1.intersection(&keys2) {
        let ty1 = labels1.get(*key).unwrap();
        let ty2 = labels2.get(*key).unwrap();
        if !try_unify_one_way(ty1, ty2, cons, var_gen, loc) {
            return false;
        }
    }

    if !extras1.is_empty() {
        return false;
    }

    if !extras2.is_empty() {
        match &extension1 {
            Some(Ty::UVar(var)) => {
                extension1 = Some(Ty::UVar(link_variant_extension(
                    &extras2, &labels2, var, var_gen, loc,
                )));
            }
            _ => {
                return false;
            }
        }
    }

    fn unit_row() -> Ty {
        Ty::Variant {
            labels: Default::default(),
            extension: None,
            is_row: true,
        }
    }

    match (extension1, extension2) {
        (None, None) => true,
        (Some(ext1), None) => try_unify_one_way(&ext1, &unit_row(), cons, var_gen, loc),
        (None, Some(_)) => false,
        (Some(ext1), Some(ext2)) => try_unify_one_way(&ext1, &ext2, cons, var_gen, loc),
    }
}

fn link_record_extension(
    extra_labels: &HashSet<&&Name>,
    label_values: &OrdMap<Name, Ty>,
    var: &UVarRef,
    var_gen: &UVarGen,
    loc: &ast::Loc,
) -> UVarRef {
    let extension_labels: OrdMap<Name, Ty> = extra_labels
        .iter()
        .map(|extra_field| {
            (
                (**extra_field).clone(),
                label_values.get(**extra_field).unwrap().clone(),
            )
        })
        .collect();
    let new_extension_var = var_gen.new_var(Kind::Row(RecordOrVariant::Record), loc.clone());
    let new_extension_ty = Ty::Record {
        labels: extension_labels,
        extension: Some(Box::new(Ty::UVar(new_extension_var.clone()))),
        is_row: true,
    };
    var.set_link(new_extension_ty);
    new_extension_var
}

fn link_variant_extension(
    extra_labels: &HashSet<&&Id>,
    label_values: &OrdMap<Id, Ty>,
    var: &UVarRef,
    var_gen: &UVarGen,
    loc: &ast::Loc,
) -> UVarRef {
    let extension_labels: OrdMap<Id, Ty> = extra_labels
        .iter()
        .map(|extra_field| {
            (
                (**extra_field).clone(),
                label_values.get(**extra_field).unwrap().clone(),
            )
        })
        .collect();
    let new_extension_var = var_gen.new_var(Kind::Row(RecordOrVariant::Variant), loc.clone());
    let new_extension_ty = Ty::Variant {
        labels: extension_labels,
        extension: Some(Box::new(Ty::UVar(new_extension_var.clone()))),
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
    trait_env: &TraitEnv,
    var_gen: &UVarGen,
    loc: &ast::Loc,
    local_assoc_tys: &[Pred],
    preds: &mut Vec<Pred>,
) -> Ty {
    if let Some(expected_ty) = expected_ty {
        unify(
            &ty,
            expected_ty,
            cons,
            trait_env,
            var_gen,
            loc,
            local_assoc_tys,
            preds,
        );
    }
    ty
}

fn link_var(var: &UVarRef, ty: &Ty) {
    // TODO: Occurs check.
    var.set_link(ty.clone());
}
