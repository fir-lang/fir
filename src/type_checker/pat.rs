use crate::ast::{self, Id};
use crate::collections::*;
use crate::type_checker::apply::apply_con_ty;
use crate::type_checker::ty::*;
use crate::type_checker::unification::unify;
use crate::type_checker::{TcFunState, loc_display};

/// Infer type of the pattern, add variables bound by the pattern to `env`.
///
/// `pat` is `mut` to be able to add types of variables and type arguments of constructors.
pub(super) fn check_pat(tc_state: &mut TcFunState, pat: &mut ast::L<ast::Pat>, level: u32) -> Ty {
    match &mut pat.node {
        ast::Pat::Var(ast::VarPat { var, ty }) => {
            assert!(ty.is_none());
            let fresh_ty = Ty::Var(tc_state.var_gen.new_var(level, Kind::Star, pat.loc.clone()));
            *ty = Some(fresh_ty.clone());
            tc_state.env.insert(var.clone(), fresh_ty.clone());
            fresh_ty
        }

        ast::Pat::Ignore => Ty::Var(tc_state.var_gen.new_var(level, Kind::Star, pat.loc.clone())),

        ast::Pat::Constr(ast::ConstrPattern {
            constr:
                ast::Constructor {
                    ty: pat_ty_name,
                    constr: pat_con_name,
                    user_ty_args,
                    ty_args,
                },
            fields: pat_fields,
            ignore_rest,
        }) => {
            assert!(ty_args.is_empty());
            assert!(user_ty_args.is_empty());

            let ty_con: &TyCon = tc_state.tys.tys.get_con(pat_ty_name).unwrap_or_else(|| {
                panic!("{}: Undefined type {}", loc_display(&pat.loc), pat_ty_name)
            });

            // Check that `con` exists and field shapes match.
            let con_scheme = match &ty_con.details {
                TyConDetails::Type(TypeDetails { cons, sum }) => match pat_con_name {
                    Some(pat_con_name) => {
                        if !*sum {
                            panic!(
                                "{}: Type {} is not a sum type",
                                loc_display(&pat.loc),
                                ty_con.id
                            )
                        }
                        if !cons
                            .iter()
                            .any(|con| con.name.as_ref() == Some(pat_con_name))
                        {
                            panic!(
                                "{}: Type {} does not have a constructor named {}",
                                loc_display(&pat.loc),
                                ty_con.id,
                                pat_con_name,
                            )
                        }
                        tc_state.tys.associated_fn_schemes
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
                                    ty_con.id,
                                    pat_con_name
                                ))
                    }
                    None => {
                        if cons.is_empty() {
                            panic!(
                                "{}: Type {} doesn't have any constructors",
                                loc_display(&pat.loc),
                                ty_con.id
                            );
                        }
                        tc_state.tys.top_schemes.get(&ty_con.id).unwrap_or_else(|| {
                            panic!(
                                "{}: BUG: type {} doesn't have a top-level scheme",
                                loc_display(&pat.loc),
                                ty_con.id
                            )
                        })
                    }
                },

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
            let (con_ty, con_ty_args) =
                con_scheme.instantiate(level, tc_state.var_gen, tc_state.preds, &pat.loc);

            *ty_args = con_ty_args.into_iter().map(Ty::Var).collect();

            // If consturctor takes named arguments, fields pattern need to be named, or a variable
            // pattern, as shorthand for `foo = foo`.
            // Update shorthands to the long form to keep things simple in `apply_con_ty`.
            if let Ty::Fun { args, .. } = &con_ty
                && args.is_named()
            {
                for pat_field in pat_fields.iter_mut() {
                    if let ast::Named {
                        name: None,
                        node:
                            ast::L {
                                node: ast::Pat::Var(var_pat),
                                ..
                            },
                    } = pat_field
                    {
                        pat_field.name = Some(var_pat.var.clone());
                    }
                }
            }

            // Apply argument pattern types to the function type.
            let pat_field_tys: Vec<ast::Named<Ty>> = pat_fields
                .iter_mut()
                .map(|ast::Named { name, node }| ast::Named {
                    name: name.clone(),
                    node: check_pat(tc_state, node, level),
                })
                .collect();

            apply_con_ty(
                &con_ty,
                &pat_field_tys,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                &pat.loc,
                *ignore_rest,
            )
        }

        ast::Pat::Record(ast::RecordPattern {
            fields,
            ignore_rest,
            inferred_ty,
        }) => {
            assert!(inferred_ty.is_none());

            let extension: Option<Box<Ty>> = if *ignore_rest {
                Some(Box::new(Ty::Var(tc_state.var_gen.new_var(
                    level,
                    Kind::Row(RecordOrVariant::Record),
                    pat.loc.clone(),
                ))))
            } else {
                None
            };

            // Similar to constructor patterns, update unnamed variable pattern `foo` as shorthand
            // for `foo = foo`.
            for field in fields.iter_mut() {
                if field.name.is_some() {
                    continue;
                }

                if let ast::Pat::Var(var_pat) = &field.node.node {
                    field.name = Some(var_pat.var.clone());
                } else {
                    panic!(
                        "{}: Record pattern with unnamed field",
                        loc_display(&field.node.loc)
                    )
                }
            }

            let ty = Ty::Anonymous {
                labels: fields
                    .iter_mut()
                    .map(|named| {
                        (
                            named.name.as_ref().unwrap().clone(),
                            check_pat(tc_state, &mut named.node, level),
                        )
                    })
                    .collect(),
                extension,
                kind: RecordOrVariant::Record,
                is_row: false,
            };
            *inferred_ty = Some(ty.clone());
            ty
        }

        ast::Pat::Str(_) => Ty::str(),

        ast::Pat::Char(_) => Ty::char(),

        ast::Pat::Or(pat1, pat2) => {
            // Collect binders for `pat1` and `pat2` in separate envs.
            tc_state.env.enter();
            let pat1_ty = check_pat(tc_state, pat1, level);
            let pat1_binders = tc_state.env.exit();

            tc_state.env.enter();
            let pat2_ty = check_pat(tc_state, pat2, level);
            let pat2_binders = tc_state.env.exit();

            // Check that patterns bind the same variables.
            let pat1_binder_keys: Set<&Id> = pat1_binders.keys().collect();
            let pat2_binder_keys: Set<&Id> = pat2_binders.keys().collect();

            if pat1_binder_keys != pat2_binder_keys {
                let mut left_vars: Vec<Id> =
                    pat1_binder_keys.iter().map(|id| (*id).clone()).collect();
                left_vars.sort();
                let mut right_vars: Vec<Id> =
                    pat2_binder_keys.iter().map(|id| (*id).clone()).collect();
                right_vars.sort();
                panic!(
                    "{}: Or pattern alternatives bind different set of variables:
                     Left = {}
                     Right = {}",
                    loc_display(&pat.loc),
                    left_vars.join(", "),
                    right_vars.join(", "),
                )
            }

            // Unify pattern binders to make sure they bind the values with same types.
            for binder in pat1_binder_keys {
                let ty1 = pat1_binders.get(binder).unwrap();
                let ty2 = pat2_binders.get(binder).unwrap();
                unify(
                    ty1,
                    ty2,
                    tc_state.tys.tys.cons(),
                    tc_state.var_gen,
                    level,
                    &pat.loc,
                );
            }

            // Add bound variables back to the env.
            for (k, v) in pat1_binders {
                tc_state.env.insert(k, v);
            }

            unify(
                &pat1_ty,
                &pat2_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                &pat.loc,
            );

            pat1_ty
        }

        ast::Pat::Variant(var_pat) => {
            let pat_ty = check_pat(tc_state, var_pat, level);
            crate::type_checker::expr::make_variant(tc_state, pat_ty, level, &pat.loc)
        }
    }
}
