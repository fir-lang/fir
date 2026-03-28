use crate::ast::{self, Id};
use crate::collections::OrdMap;
use crate::type_checker::unification::unify;
use crate::type_checker::*;
use crate::utils::loc_display;

/// Apply a constructor type to arguments to get a pattern type.
///
/// The constructor type should be a function type if it takes arguments. Otherwise `args` should be
/// empty.
pub(crate) fn apply_con_ty(
    tc_state: &mut TcFunState,
    // Type of the constructor being applied.
    con_ty: &Ty,
    // Types of the arguments passed to the constructor.
    args: &Vec<ast::Named<Ty>>,
    // The `..binder` part of the pattern.
    rest: &mut ast::RestPat,
    level: u32,
    loc: &ast::Loc,
) -> Ty {
    match con_ty {
        Ty::Fun {
            args: con_ty_args,
            ret: con_ty_ret,
            exceptions: con_ty_exceptions,
        } => {
            // This function is only called on constructors, which don't have exception types.
            assert!(con_ty_exceptions.is_none());

            match con_ty_args {
                FunArgs::Positional { args: con_ty_args } => {
                    if (matches!(rest, ast::RestPat::No) && con_ty_args.len() != args.len())
                        || args.len() > con_ty_args.len()
                    {
                        panic!(
                            "{}: Constructor takes {} positional arguments, but applied {}",
                            loc_display(loc),
                            con_ty_args.len(),
                            args.len()
                        );
                    }
                    for (ty1, ty2) in con_ty_args.iter().zip(args.iter()) {
                        if let Some(name) = &ty2.name {
                            panic!(
                                "{}: Constructor takes positional arguments, but applied named argument '{}'",
                                loc_display(loc),
                                name
                            );
                        }
                        unify(
                            ty1,
                            &ty2.node,
                            tc_state.tys.tys.cons(),
                            tc_state.trait_env,
                            tc_state.var_gen,
                            level,
                            loc,
                            tc_state.assumps,
                            tc_state.preds,
                        );
                    }
                }

                FunArgs::Named {
                    args: con_ty_args,
                    extension: con_ty_extension,
                } => {
                    // Names of fields in the pattern.
                    let mut arg_names: HashSet<&Id> = Default::default();

                    // Names in the patterns that are not in the function's type.
                    let mut extra_pat_fields: OrdMap<Id, Ty> = OrdMap::new();

                    for arg in args {
                        let name = match arg.name.as_ref() {
                            Some(name) => name,
                            None => {
                                panic!(
                                    "{}: Constructor takes named arguments, but passed positional argument",
                                    loc_display(loc)
                                );
                            }
                        };
                        if !arg_names.insert(name) {
                            panic!(
                                "{}: Named argument '{}' applied multiple times",
                                loc_display(loc),
                                name,
                            );
                        }
                        if let Some(con_ty_arg) = con_ty_args.get(name) {
                            unify(
                                con_ty_arg,
                                &arg.node,
                                tc_state.tys.tys.cons(),
                                tc_state.trait_env,
                                tc_state.var_gen,
                                level,
                                loc,
                                tc_state.assumps,
                                tc_state.preds,
                            );
                        } else if con_ty_extension.is_some() {
                            extra_pat_fields.insert(name.clone(), arg.node.clone());
                        } else {
                            panic!(
                                "{}: Constructor doesn't take named argument '{}'",
                                loc_display(loc),
                                name,
                            );
                        }
                    }

                    // Check that all known args are provided (unless we bind/ignore extra fields).
                    if matches!(rest, ast::RestPat::No) {
                        // Constructor's parameter names.
                        let con_ty_arg_names: HashSet<&Id> = con_ty_args.keys().collect();

                        // Names of arguments being passed.
                        let passed_arg_names: HashSet<&Id> = arg_names
                            .iter()
                            .filter(|n| con_ty_args.contains_key(**n))
                            .copied()
                            .collect();

                        // Without the `..rest` part in the pattern the names must match.
                        if con_ty_arg_names != passed_arg_names {
                            let con_args_str = con_ty_arg_names
                                .iter()
                                .map(ToString::to_string)
                                .collect::<Vec<String>>()
                                .join(", ");
                            let applied_args_str = arg_names
                                .iter()
                                .map(ToString::to_string)
                                .collect::<Vec<String>>()
                                .join(", ");
                            panic!(
                                "{}: Constructor takes named arguments {{{}}}, but applied {{{}}}",
                                loc_display(loc),
                                con_args_str,
                                applied_args_str
                            );
                        }
                    }

                    // Unify extra fields with the constructor's function type's extension type.
                    match con_ty_extension {
                        None => {
                            // This case should be handled above.
                            assert!(extra_pat_fields.is_empty());
                            if let ast::RestPat::Bind(ast::VarPat { var, ty, refined }) = rest {
                                assert!(ty.is_none());
                                assert!(refined.is_none());

                                // Argument patterns already unified with the constructor parameter
                                // types.

                                // Constructor's parameter names.
                                let con_ty_arg_names: HashSet<&Id> = con_ty_args.keys().collect();

                                let unmatched_field_names: HashSet<&&Id> =
                                    con_ty_arg_names.difference(&arg_names).collect();

                                let rest_ty = Ty::Anonymous {
                                    labels: unmatched_field_names
                                        .iter()
                                        .map(|field_name| {
                                            (
                                                (**field_name).clone(),
                                                con_ty_args.get(**field_name).unwrap().clone(),
                                            )
                                        })
                                        .collect(),
                                    extension: None,
                                    record_or_variant: RecordOrVariant::Record,
                                    is_row: false,
                                };

                                tc_state.env.insert(var.clone(), rest_ty.clone());
                                *ty = Some(rest_ty.clone());
                            }
                        }
                        Some(con_ty_extension) => {
                            // Constructor takes named arguments, and has a row extension. E.g.
                            // `Fn(x: U32, y: U32, ..r) Ret[r]`. In this case the pattern can have
                            // extra fields, they go into the extension.
                            let row_extension: Option<Box<Ty>> = match rest {
                                ast::RestPat::Ignore => {
                                    Some(Box::new(Ty::UVar(tc_state.var_gen.new_var(
                                        level,
                                        Kind::Row(RecordOrVariant::Record),
                                        loc.clone(),
                                    ))))
                                }
                                ast::RestPat::Bind(ast::VarPat { var, ty, refined }) => {
                                    assert!(ty.is_none());
                                    assert!(refined.is_none());
                                    let row_ty = Ty::UVar(tc_state.var_gen.new_var(
                                        level,
                                        Kind::Row(RecordOrVariant::Record),
                                        loc.clone(),
                                    ));
                                    let binder_ty = Ty::Anonymous {
                                        labels: Default::default(),
                                        extension: Some(Box::new(row_ty.clone())),
                                        record_or_variant: RecordOrVariant::Record,
                                        is_row: false,
                                    };
                                    tc_state.env.insert(var.clone(), binder_ty.clone());
                                    *ty = Some(binder_ty.clone());
                                    Some(Box::new(row_ty))
                                }
                                ast::RestPat::No => None,
                            };
                            let extra_row = Ty::Anonymous {
                                labels: extra_pat_fields,
                                extension: row_extension,
                                record_or_variant: RecordOrVariant::Record,
                                is_row: true,
                            };
                            unify(
                                con_ty_extension,
                                &extra_row,
                                tc_state.tys.tys.cons(),
                                tc_state.trait_env,
                                tc_state.var_gen,
                                level,
                                loc,
                                tc_state.assumps,
                                tc_state.preds,
                            );
                        }
                    }
                }
            }

            (**con_ty_ret).clone()
        }

        Ty::UVar(_)
        | Ty::Con(_, _)
        | Ty::RVar(_, _)
        | Ty::App(_, _, _)
        | Ty::Anonymous { .. }
        | Ty::QVar(_, _)
        | Ty::AssocTySelect { .. } => {
            if args.is_empty() {
                return con_ty.clone();
            }
            panic!(
                "{}: Type {} doesn't take arguments, but applied {} arguments",
                loc_display(loc),
                con_ty,
                args.len(),
            )
        }
    }
}
