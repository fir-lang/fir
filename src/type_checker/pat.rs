use crate::ast::{self, Id};
use crate::collections::{Map, Set};
use crate::type_checker::apply::apply;
use crate::type_checker::ty::*;
use crate::type_checker::unification::unify;
use crate::type_checker::{loc_display, TcFunState};

/// Infer type of the pattern, add variables bound by the pattern to `env`.
pub(super) fn check_pat(tc_state: &mut TcFunState, pat: &mut ast::L<ast::Pat>, level: u32) -> Ty {
    match &mut pat.node {
        ast::Pat::Var(var) => {
            let ty = Ty::Var(tc_state.var_gen.new_var(level, Kind::Star, pat.loc.clone()));
            tc_state.env.insert(var.clone(), ty.clone());
            ty
        }

        ast::Pat::Ignore => Ty::Var(tc_state.var_gen.new_var(level, Kind::Star, pat.loc.clone())),

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

            let ty_con: &TyCon = tc_state
                .tys
                .tys
                .get_con(pat_ty_name)
                .unwrap_or_else(|| panic!("{}: Undefined type", loc_display(&pat.loc)));

            // Check that `con` exists and field shapes match.
            let con_scheme = match &ty_con.details {
                TyConDetails::Type(TypeDetails { cons }) => {
                    check_pat_shape(pat_ty_name, pat_con_name, pat_fields, &pat.loc, cons);
                    match pat_con_name {
                        Some(pat_con_name) =>
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
                                    &ty_con.id,
                                    pat_con_name
                                )),
                        None =>
                            tc_state.tys.top_schemes.get(&ty_con.id).unwrap_or_else(|| panic!(
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
            let (con_ty, con_ty_args) =
                con_scheme.instantiate(level, tc_state.var_gen, tc_state.preds, &pat.loc);
            *ty_args = con_ty_args.into_iter().map(Ty::Var).collect();

            // Apply argument pattern types to the function type.
            let pat_field_tys: Vec<ast::Named<Ty>> = pat_fields
                .iter_mut()
                .map(|ast::Named { name, node }| ast::Named {
                    name: name.clone(),
                    node: check_pat(tc_state, node, level),
                })
                .collect();

            apply(
                &con_ty,
                &pat_field_tys,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                &pat.loc,
            )
        }

        ast::Pat::Record(fields) => {
            let extension_var = Ty::Var(tc_state.var_gen.new_var(
                level,
                Kind::Row(RecordOrVariant::Record),
                pat.loc.clone(),
            ));
            Ty::Anonymous {
                labels: fields
                    .iter_mut()
                    .map(|named| {
                        (
                            named.name.as_ref().unwrap().clone(),
                            check_pat(tc_state, &mut named.node, level),
                        )
                    })
                    .collect(),
                extension: Some(Box::new(extension_var)),
                kind: RecordOrVariant::Record,
                is_row: false,
            }
        }

        ast::Pat::Variant(ast::VariantPattern { constr, fields }) => {
            let extension_var = Ty::Var(tc_state.var_gen.new_var(
                level,
                Kind::Row(RecordOrVariant::Variant),
                pat.loc.clone(),
            ));

            let mut arg_tys: Map<Id, Ty> =
                Map::with_capacity_and_hasher(fields.len(), Default::default());

            for ast::Named { name, node } in fields.iter_mut() {
                let name = match name {
                    Some(name) => name,
                    None => panic!(
                        "{}: Variant pattern with unnamed args not supported yet",
                        loc_display(&pat.loc)
                    ),
                };
                let ty = check_pat(tc_state, node, level);
                let old = arg_tys.insert(name.clone(), ty);
                if old.is_some() {
                    panic!(
                        "{}: Variant pattern with dupliate fields",
                        loc_display(&pat.loc)
                    );
                }
            }

            let record_ty = Ty::Anonymous {
                labels: arg_tys,
                extension: None,
                kind: RecordOrVariant::Record,
                is_row: false,
            };

            Ty::Anonymous {
                labels: [(constr.clone(), record_ty)].into_iter().collect(),
                extension: Some(Box::new(extension_var)),
                kind: RecordOrVariant::Variant,
                is_row: false,
            }
        }

        ast::Pat::Str(_) => Ty::str(),

        ast::Pat::StrPfx(_, var) => {
            tc_state.env.insert(var.clone(), Ty::str());
            Ty::str()
        }

        ast::Pat::Char(_) => Ty::char(),

        ast::Pat::Or(pat1, pat2) => {
            let pat1_ty = check_pat(tc_state, pat1, level);
            let pat2_ty = check_pat(tc_state, pat2, level);
            // TODO: Check that the patterns bind the same variables of same types.
            // TODO: Any other checks here?
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
    }
}

fn check_pat_shape(
    pat_ty_name: &Id,
    pat_con_name: &Option<Id>,
    pat_fields: &[ast::Named<ast::L<ast::Pat>>],
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
