use crate::ast::{self, Id};
use crate::collections::OrdMap;
use crate::type_checker::traits::TraitEnv;
use crate::type_checker::unification::unify;
use crate::type_checker::*;
use crate::utils::loc_display;

/// Apply a constructor type to arguments.
///
/// The constructor type should be a function type if it takes arguments. Otherwise `args` should be
/// empty.
pub(crate) fn apply_con_ty(
    con_ty: &Ty,
    args: &Vec<ast::Named<Ty>>,
    cons: &ScopeMap<Id, TyCon>,
    trait_env: &TraitEnv,
    var_gen: &UVarGen,
    level: u32,
    loc: &ast::Loc,
    ignore_rest: bool,
    local_assoc_tys: &[Pred],
    preds: &mut Vec<Pred>,
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
                FunArgs::Positional {
                    args: con_ty_args, ..
                } => {
                    if (!ignore_rest && con_ty_args.len() != args.len())
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
                            cons,
                            trait_env,
                            var_gen,
                            level,
                            loc,
                            local_assoc_tys,
                            preds,
                        );
                    }
                }

                FunArgs::Named {
                    args: con_ty_args,
                    extension,
                } => {
                    let mut arg_names: HashSet<&Id> = Default::default();
                    let mut extra_fields: OrdMap<Id, Ty> = OrdMap::new();

                    for arg in args {
                        let name = match arg.name.as_ref() {
                            Some(name) => name,
                            None => {
                                panic!(
                                    "{}: Constructor takes named arguments, but applied positional argument",
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
                                cons,
                                trait_env,
                                var_gen,
                                level,
                                loc,
                                local_assoc_tys,
                                preds,
                            );
                        } else if extension.is_some() {
                            extra_fields.insert(name.clone(), arg.node.clone());
                        } else {
                            panic!(
                                "{}: Constructor doesn't take named argument '{}'",
                                loc_display(loc),
                                name,
                            );
                        }
                    }

                    // Check that all known args are provided (unless ignore_extra).
                    if !ignore_rest {
                        let con_ty_arg_names: HashSet<&Id> = con_ty_args.keys().collect();
                        let known_arg_names: HashSet<&Id> = arg_names
                            .iter()
                            .filter(|n| con_ty_args.contains_key(**n))
                            .copied()
                            .collect();
                        if con_ty_arg_names != known_arg_names {
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

                    // Unify extra fields with the extension type.
                    match extension {
                        None => {
                            // This case should be handled above.
                            assert!(extra_fields.is_empty());
                        }
                        Some(ext_ty) => {
                            let row_extension = if ignore_rest {
                                Some(Box::new(Ty::UVar(var_gen.new_var(
                                    level,
                                    Kind::Row(RecordOrVariant::Record),
                                    loc.clone(),
                                ))))
                            } else {
                                None
                            };
                            let extra_row = Ty::Anonymous {
                                labels: extra_fields,
                                extension: row_extension,
                                kind: RecordOrVariant::Record,
                                is_row: true,
                            };
                            unify(
                                ext_ty,
                                &extra_row,
                                cons,
                                trait_env,
                                var_gen,
                                level,
                                loc,
                                local_assoc_tys,
                                preds,
                            );
                        }
                    }
                }
            }

            (**con_ty_ret).clone()
        }

        Ty::UVar(_)
        | Ty::Con(_, _)
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
