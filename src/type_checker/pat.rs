use crate::ast::{self, Id};
use crate::collections::Set;
use crate::scope_map::ScopeMap;
use crate::type_checker::apply::apply;
use crate::type_checker::ty::*;
use crate::type_checker::unification::unify;
use crate::type_checker::{loc_display, PgmTypes};

use smol_str::SmolStr;

/// Infer type of the pattern, add variables bound by the pattern to `env`.
pub(super) fn check_pat(
    pat: &mut ast::L<ast::Pat>,
    level: u32,
    env: &mut ScopeMap<Id, Ty>,
    var_gen: &mut TyVarGen,
    tys: &PgmTypes,
    preds: &mut PredSet,
) -> Ty {
    match &mut pat.node {
        ast::Pat::Var(var) => {
            let ty = Ty::Var(var_gen.new_var(level, pat.loc.clone()));
            env.insert(var.clone(), ty.clone());
            ty
        }

        ast::Pat::Ignore => Ty::Var(var_gen.new_var(level, pat.loc.clone())),

        ast::Pat::Constr(ast::ConstrPattern {
            constr:
                ast::Constructor {
                    type_: pat_ty_name,
                    constr: pat_con_name,
                },
            fields: pat_fields,
            ty_args,
        }) => {
            debug_assert!(ty_args.is_empty());

            let ty_con: &TyCon = tys
                .tys
                .get_con(pat_ty_name)
                .unwrap_or_else(|| panic!("{}: Undefined type", loc_display(&pat.loc)));

            // Check that `con` exists and field shapes match.
            let con_scheme = match &ty_con.details {
                TyConDetails::Type(TypeDetails { cons }) => {
                    check_pat_shape(pat_ty_name, pat_con_name, pat_fields, &pat.loc, cons);
                    match pat_con_name {
                        Some(pat_con_name) =>
                            tys.associated_fn_schemes
                                .get(&ty_con.id)
                                .unwrap_or_else(|| panic!(
                                    "{}: BUG: Type {} doesn't have any schemes",
                                    loc_display(&pat.loc),
                                    ty_con.id
                                ))
                                .get(pat_con_name)
                                .unwrap_or_else(|| panic!(
                                    "{}: BUG: Type {} doesn't have a constructor named {} in associated schemes",
                                    loc_display(&pat.loc),
                                    &ty_con.id,
                                    pat_con_name
                                )),
                        None =>
                            tys.top_schemes.get(&ty_con.id).unwrap_or_else(|| panic!(
                                "{}: BUG: type {} doesn't have a top-level scheme",
                                loc_display(&pat.loc),
                                &ty_con.id
                            )),
                    }
                }

                TyConDetails::Trait { .. } => panic!(
                    "{}: Type constructor {} is a trait",
                    loc_display(&pat.loc),
                    pat_ty_name
                ),

                TyConDetails::Synonym(_) => panic!(
                    "{}: Type constructor {} is a type synonym",
                    loc_display(&pat.loc),
                    pat_ty_name
                ),
            };

            // We don't need to instantiate based on pattern types. If we don't have a term with
            // the type the pattern will never match.
            let (con_ty, con_ty_args) = con_scheme.instantiate(level, var_gen, preds, &pat.loc);
            *ty_args = con_ty_args.into_iter().map(Ty::Var).collect();

            // Apply argument pattern types to the function type.
            let pat_field_tys: Vec<ast::Named<Ty>> = pat_fields
                .iter_mut()
                .map(|ast::Named { name, node }| ast::Named {
                    name: name.clone(),
                    node: check_pat(node, level, env, var_gen, tys, preds),
                })
                .collect();

            apply(&con_ty, &pat_field_tys, tys.tys.cons(), &pat.loc)
        }

        ast::Pat::Record(fields) => Ty::Record(
            fields
                .iter_mut()
                .map(|named| {
                    (
                        named.name.as_ref().unwrap().clone(),
                        check_pat(&mut named.node, level, env, var_gen, tys, preds),
                    )
                })
                .collect(),
        ),

        ast::Pat::Str(_) => {
            let pat_ty = var_gen.new_var(level, pat.loc.clone());
            preds.add(
                Pred {
                    ty_var: pat_ty.clone(),
                    trait_: Ty::to_str_id(),
                    assoc_tys: Default::default(),
                },
                &pat.loc,
            );
            Ty::Var(pat_ty)
        }

        ast::Pat::StrPfx(_, var) => {
            // Pattern may be a `Str` or `StrView`, `var` will be `StrView`.
            let pat_ty = var_gen.new_var(level, pat.loc.clone());
            preds.add(
                Pred {
                    ty_var: pat_ty.clone(),
                    trait_: Ty::to_str_id(),
                    assoc_tys: Default::default(),
                },
                &pat.loc,
            );

            env.insert(var.clone(), Ty::str());

            Ty::Var(pat_ty)
        }

        ast::Pat::Char(_) => Ty::Con(SmolStr::new_static("Char")),

        ast::Pat::Or(pat1, pat2) => {
            let pat1_ty = check_pat(pat1, level, env, var_gen, tys, preds);
            let pat2_ty = check_pat(pat2, level, env, var_gen, tys, preds);
            // TODO: Check that the patterns bind the same variables of same types.
            // TODO: Any other checks here?
            unify(&pat1_ty, &pat2_ty, tys.tys.cons(), &pat.loc);
            pat1_ty
        }
    }
}

fn check_pat_shape(
    pat_ty_name: &Id,
    pat_con_name: &Option<Id>,
    pat_fields: &[ast::Named<Box<ast::L<ast::Pat>>>],
    loc: &ast::Loc,
    cons: &[ConShape],
) {
    let pat_con_name = match pat_con_name {
        Some(pat_con_name) => pat_con_name,
        None => {
            if cons.len() != 1 || (cons.len() == 1 && cons[0].name.is_some()) {
                panic!(
                    "{}: Type {} does not have unnamed constructor",
                    loc_display(loc),
                    pat_ty_name
                );
            }
            return;
        }
    };

    let mut shape_checked = false;
    for con in cons {
        if let Some(con_name) = &con.name {
            if con_name != pat_con_name {
                continue;
            }

            shape_checked = true;
            match &con.fields {
                ConFieldShape::Unnamed(arity) => {
                    for pat_field in pat_fields {
                        if pat_field.name.is_some() {
                            panic!(
                                "{}: Constructor {} does not have named fields",
                                loc_display(loc),
                                con_name
                            );
                        }
                    }
                    if pat_fields.len() != *arity as usize {
                        panic!(
                            "{}: Constructor {} has {} fields, but pattern bind {}",
                            loc_display(loc),
                            con_name,
                            arity,
                            pat_fields.len()
                        );
                    }
                }
                ConFieldShape::Named(names) => {
                    let mut pat_field_names: Set<&Id> = Default::default();
                    for pat_field in pat_fields {
                        match &pat_field.name {
                            Some(pat_field_name) => {
                                if !names.contains(pat_field_name) {
                                    panic!(
                                        "{}: Constructor {} does not have named field {}",
                                        loc_display(loc),
                                        con_name,
                                        pat_field_name
                                    );
                                }
                                if !pat_field_names.insert(pat_field_name) {
                                    panic!(
                                        "{}: Pattern binds named field {} multiple times",
                                        loc_display(loc),
                                        pat_field_name
                                    );
                                }
                            }
                            None => {
                                panic!(
                                    "{}: Constructor {} has named fields, but pattern has unnamed field",
                                    loc_display(loc),
                                    con_name
                                );
                            }
                        }
                    }
                }
            }
        }
    }
    if !shape_checked {
        panic!(
            "{}: Type {} does not have constructor {}",
            loc_display(loc),
            pat_ty_name,
            pat_con_name
        );
    }
}
