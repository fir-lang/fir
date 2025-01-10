use crate::ast::{self, Id};
use crate::collections::{Map, Set};
use crate::type_checker::apply::apply;
use crate::type_checker::pat_coverage::PatCoverage;
use crate::type_checker::row_utils::collect_rows;
use crate::type_checker::ty::*;
use crate::type_checker::unification::unify;
use crate::type_checker::{loc_display, TcFunState};

/// Infer type of the pattern, add variables bound by the pattern to `env`.
///
/// `pat` is `mut` to be able to update type arguments in constructor patterns with fresh type
/// variables of the constructor's instantiated type's arguments.
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

pub(super) fn refine_pat_binders(
    tc_state: &mut TcFunState,
    ty: &Ty,                // type of the value being matched
    pat: &ast::L<ast::Pat>, // the pattern being refined
    coverage: &PatCoverage, // coverage information of `pat`
) {
    match &pat.node {
        ast::Pat::Var(var) => {
            let (labels, extension) = match ty.normalize(tc_state.tys.tys.cons()) {
                Ty::Anonymous {
                    labels,
                    extension,
                    kind: RecordOrVariant::Variant,
                    is_row,
                } => {
                    assert!(!is_row);
                    collect_rows(
                        tc_state.tys.tys.cons(),
                        ty,
                        RecordOrVariant::Variant,
                        &labels,
                        extension.clone(),
                    )
                }
                _ => return,
            };

            let num_labels = labels.len();

            let mut unhandled_labels: Map<Id, Ty> =
                Map::with_capacity_and_hasher(num_labels, Default::default());

            'variant_label_loop: for (label, label_ty) in labels {
                let label_field_coverage = match coverage.get_variant_fields(&label) {
                    Some(field_coverage) => field_coverage,
                    None => {
                        unhandled_labels.insert(label, label_ty);
                        continue;
                    }
                };

                let (label_fields, label_field_extension) =
                    match &label_ty.normalize(tc_state.tys.tys.cons()) {
                        ty @ Ty::Anonymous {
                            labels,
                            extension,
                            kind,
                            is_row,
                        } => {
                            assert!(!is_row);
                            assert_eq!(*kind, RecordOrVariant::Record);
                            collect_rows(
                                tc_state.tys.tys.cons(),
                                ty,
                                RecordOrVariant::Record,
                                labels,
                                extension.clone(),
                            )
                        }

                        _ => return,
                    };

                assert!(label_field_extension.is_none());

                for (field_label, field_ty) in label_fields {
                    let field_coverage = match label_field_coverage.get_named_field(&field_label) {
                        Some(field_coverage) => field_coverage,
                        None => {
                            unhandled_labels.insert(label, label_ty);
                            continue 'variant_label_loop;
                        }
                    };

                    if !field_coverage.is_exhaustive(&field_ty, tc_state, &pat.loc) {
                        unhandled_labels.insert(label, label_ty);
                        continue 'variant_label_loop;
                    }
                }
            }

            if unhandled_labels.len() != num_labels {
                let new_variant = Ty::Anonymous {
                    labels: unhandled_labels,
                    extension: extension.map(Box::new),
                    kind: RecordOrVariant::Variant,
                    is_row: false,
                };

                tc_state.env.insert(var.clone(), new_variant);
            }
        }

        ast::Pat::Constr(ast::ConstrPattern {
            constr: ast::Constructor { type_, constr },
            fields: field_pats,
            ty_args: _,
        }) => {
            let con_field_coverage = match coverage.get_con_fields(type_, constr.as_ref()) {
                Some(coverage) => coverage,
                None => return,
            };

            let con_scheme = match constr {
                Some(con_id) => tc_state
                    .tys
                    .associated_fn_schemes
                    .get(type_)
                    .unwrap()
                    .get(con_id)
                    .unwrap(),
                None => tc_state.tys.top_schemes.get(type_).unwrap(),
            };

            let con_ty = match ty.normalize(tc_state.tys.tys.cons()) {
                Ty::Con(con_id) => {
                    assert_eq!(&con_id, type_);
                    assert!(con_scheme.quantified_vars.is_empty());

                    // or just `con_scheme.ty`.
                    con_scheme.subst_qvars(&Default::default())
                }

                Ty::App(con_id, ty_args) => {
                    assert_eq!(&con_id, type_);
                    let ty_args = match ty_args {
                        TyArgs::Positional(args) => args,
                        TyArgs::Named(_) => panic!(), // associated type syntax?
                    };

                    assert_eq!(con_scheme.quantified_vars.len(), ty_args.len());
                    let mut var_map: Map<Id, Ty> =
                        Map::with_capacity_and_hasher(ty_args.len(), Default::default());
                    for ((var_id, _qvar), ty) in
                        con_scheme.quantified_vars.iter().zip(ty_args.iter())
                    {
                        var_map.insert(var_id.clone(), ty.clone());
                    }

                    con_scheme.subst_qvars(&var_map)
                }

                Ty::Var(_)
                | Ty::QVar(_)
                | Ty::Fun { .. }
                | Ty::AssocTySelect { .. }
                | Ty::Anonymous { .. } => return,
            };

            for (field_idx, field_pat) in field_pats.iter().enumerate() {
                let field_pat_coverage = match &field_pat.name {
                    Some(field_name) => con_field_coverage.get_named_field(field_name),
                    None => con_field_coverage.get_positional_field(field_idx),
                };

                let field_pat_coverage = match field_pat_coverage {
                    Some(coverage) => coverage,
                    None => return,
                };

                let field_ty: Ty = match &con_ty {
                    Ty::Fun { args, ret: _ } => {
                        match args {
                            FunArgs::Positional(args) => {
                                if field_pat.name.is_some() {
                                    panic!() // field pattern is named, but constructor doesn't have named fields
                                }
                                args.get(field_idx).cloned().unwrap()
                            }
                            FunArgs::Named(args) => {
                                let field_name = match &field_pat.name {
                                    Some(name) => name,
                                    None => panic!(), // field pattern is not named, but constructor has named arguments
                                };
                                args.get(field_name).cloned().unwrap()
                            }
                        }
                    }

                    _ => return,
                };

                refine_pat_binders(tc_state, &field_ty, &field_pat.node, field_pat_coverage);
            } // field loop
        } // constr pattern

        ast::Pat::Variant(ast::VariantPattern {
            constr,
            fields: field_pats,
        }) => {
            let variant_field_coverage = match coverage.get_variant_fields(constr) {
                Some(coverage) => coverage,
                None => return,
            };

            let (variant_ty_labels, _) = match ty {
                Ty::Anonymous {
                    labels,
                    extension,
                    kind: RecordOrVariant::Variant,
                    is_row,
                } => {
                    assert!(!*is_row);
                    collect_rows(
                        tc_state.tys.tys.cons(),
                        ty,
                        RecordOrVariant::Variant,
                        labels,
                        extension.clone(),
                    )
                }

                _ => return,
            };

            let (variant_field_tys, _) = match variant_ty_labels.get(constr).unwrap() {
                Ty::Anonymous {
                    labels,
                    extension,
                    kind: RecordOrVariant::Record,
                    is_row,
                } => {
                    assert!(!*is_row);
                    collect_rows(
                        tc_state.tys.tys.cons(),
                        ty,
                        RecordOrVariant::Variant,
                        labels,
                        extension.clone(),
                    )
                }

                _ => return,
            };

            for field_pat in field_pats {
                let field_name = field_pat.name.clone().unwrap(); // variant fields need to be named
                let field_pat_coverage =
                    variant_field_coverage.get_named_field(&field_name).unwrap();
                let field_ty = variant_field_tys.get(&field_name).unwrap();
                refine_pat_binders(tc_state, field_ty, &field_pat.node, field_pat_coverage);
            } // field loop
        } // variant

        ast::Pat::Record(fields) => {
            let (record_labels, _) = match ty {
                Ty::Anonymous {
                    labels,
                    extension,
                    kind: RecordOrVariant::Record,
                    is_row,
                } => {
                    assert!(!*is_row);
                    collect_rows(
                        tc_state.tys.tys.cons(),
                        ty,
                        RecordOrVariant::Record,
                        labels,
                        extension.clone(),
                    )
                }

                _ => return,
            };

            for field_pat in fields {
                let field_name = field_pat.name.clone().unwrap(); // record fields need to be named
                let field_pat_coverage = match coverage.get_record_field(&field_name) {
                    Some(coverage) => coverage,
                    None => return,
                };
                let field_ty = record_labels.get(&field_name).unwrap();
                refine_pat_binders(tc_state, field_ty, &field_pat.node, field_pat_coverage);
            } // field loop
        } // record

        ast::Pat::Or(p1, p2) => {
            refine_pat_binders(tc_state, ty, p1, coverage);
            refine_pat_binders(tc_state, ty, p2, coverage);
        }

        ast::Pat::Ignore | ast::Pat::Str(_) | ast::Pat::Char(_) | ast::Pat::StrPfx(_, _) => {}
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
