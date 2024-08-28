use crate::ast;
use crate::collections::Set;
use crate::scope_map::ScopeMap;
use crate::type_checker::ty::*;
use crate::type_checker::unification::unify;
use crate::type_checker::{loc_string, PgmTypes};

use smol_str::SmolStr;

/// Infer type of the pattern, add variables bound by the pattern to `env`.
pub(super) fn check_pat(
    pat: &ast::L<ast::Pat>,
    level: u32,
    env: &mut ScopeMap<Id, Ty>,
    var_gen: &mut TyVarGen,
    tys: &PgmTypes,
    preds: &mut PredSet,
) -> Ty {
    match &pat.node {
        ast::Pat::Var(var) => {
            let ty = Ty::Var(var_gen.new_var(level, pat.loc.clone()));
            env.insert(var.clone(), ty.clone());
            ty
        }

        ast::Pat::Ignore => Ty::Var(var_gen.new_var(level, pat.loc.clone())),

        ast::Pat::Constr(ast::ConstrPattern {
            constr: ast::Constructor { type_, constr },
            fields: pat_fields,
        }) => {
            let ty_con: &TyCon = tys
                .tys
                .get_con(type_)
                .unwrap_or_else(|| panic!("{}: Undefined type", loc_string(&pat.loc)));

            let (con_scheme, con_str): (&Scheme, String) = {
                match &ty_con.details {
                    TyConDetails::Type(TypeDetails { cons: _ }) => match constr {
                        Some(constr) => (
                            tys.associated_schemes
                                .get(&ty_con.id)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "{}: BUG: Type {} doesn't have any schemes",
                                        loc_string(&pat.loc),
                                        ty_con.id
                                    )
                                })
                                .get(constr)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "{}: Type {} doesn't have a constructor named {}",
                                        loc_string(&pat.loc),
                                        &ty_con.id,
                                        constr
                                    )
                                }),
                            format!("{}.{}", ty_con.id, constr),
                        ),
                        None => (
                            tys.top_schemes.get(&ty_con.id).unwrap_or_else(|| {
                                panic!(
                                    "{}: BUG: type {} doesn't have a top-level scheme",
                                    loc_string(&pat.loc),
                                    &ty_con.id
                                )
                            }),
                            ty_con.id.to_string(),
                        ),
                    },

                    TyConDetails::Trait { .. } => panic!(
                        "{}: Type constructor {} is a trait",
                        loc_string(&pat.loc),
                        type_
                    ),

                    TyConDetails::Synonym(_) => panic!(
                        "{}: Type constructor {} is a type synonym",
                        loc_string(&pat.loc),
                        type_
                    ),
                }
            };

            let con_ty = con_scheme.instantiate(level, var_gen, preds, &pat.loc);

            match con_ty {
                Ty::Con(_) => {
                    if pat_fields.is_empty() {
                        con_ty
                    } else {
                        panic!(
                            "{}: Constructor {} does not have any fields",
                            loc_string(&pat.loc),
                            con_str
                        )
                    }
                }

                Ty::Fun(args, ret) => {
                    if args.len() != pat_fields.len() {
                        panic!(
                            "{}: Constructor {} has {} fields, but pattern has {}",
                            loc_string(&pat.loc),
                            con_str,
                            args.len(),
                            pat_fields.len()
                        );
                    }

                    for (con_ty, field_pat) in args.iter().zip(pat_fields.iter()) {
                        if field_pat.name.is_some() {
                            panic!(
                                "{}: Constructor {} has no named fields",
                                loc_string(&pat.loc),
                                con_str
                            )
                        }
                        let field_pat_ty =
                            check_pat(&field_pat.node, level, env, var_gen, tys, preds);
                        unify(con_ty, &field_pat_ty, tys.tys.cons(), &pat.loc);
                    }

                    *ret
                }

                Ty::FunNamedArgs(args, ret) => {
                    if args.len() != pat_fields.len() {
                        panic!(
                            "{}: Constructor {} has {} fields, but pattern has {}",
                            loc_string(&pat.loc),
                            con_str,
                            args.len(),
                            pat_fields.len()
                        );
                    }

                    let mut seen: Set<&Id> = Default::default();
                    for pat_field in pat_fields {
                        match &pat_field.name {
                            Some(name) => {
                                if !seen.insert(name) {
                                    panic!("{}: Field with name {} occurs multiple times in the pattern", loc_string(&pat.loc), name);
                                }
                            }
                            None => {
                                panic!(
                                    "{}: Pattern for constructor {} has unnamed argument",
                                    loc_string(&pat.loc),
                                    con_str
                                );
                            }
                        }
                    }

                    let arg_keys: Set<&Id> = args.keys().collect();
                    if seen != arg_keys {
                        panic!("{}: Constructor {} has named fields {:?}, but pattern has named fields {:?}", loc_string(&pat.loc), con_str, arg_keys, seen);
                    }

                    for (arg_name, arg_ty) in &args {
                        let field_pat = pat_fields
                            .iter()
                            .find_map(|pat_field| {
                                if pat_field.name.as_ref().unwrap() == arg_name {
                                    Some(&pat_field.node)
                                } else {
                                    None
                                }
                            })
                            .unwrap();

                        let field_pat_ty = check_pat(field_pat, level, env, var_gen, tys, preds);

                        unify(&field_pat_ty, arg_ty, tys.tys.cons(), &pat.loc);
                    }

                    *ret
                }

                other => panic!(
                    "{}: BUG: Weird constructor type: {:?}",
                    loc_string(&pat.loc),
                    other
                ),
            }
        }

        ast::Pat::Record(fields) => Ty::Record(
            fields
                .iter()
                .map(|named| {
                    (
                        named.name.as_ref().unwrap().clone(),
                        check_pat(&named.node, level, env, var_gen, tys, preds),
                    )
                })
                .collect(),
        ),

        ast::Pat::Str(_) => {
            let pat_ty = var_gen.new_var(level, pat.loc.clone());
            preds.add(
                Pred {
                    ty_var: pat_ty.clone(),
                    trait_: Ty::to_str_view_id(),
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
                    trait_: Ty::to_str_view_id(),
                    assoc_tys: Default::default(),
                },
                &pat.loc,
            );

            env.insert(var.clone(), Ty::str_view());

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
