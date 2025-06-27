use crate::ast::{self, Id};
use crate::type_checker::unification::unify;
use crate::type_checker::*;
use crate::utils::loc_display;

pub(crate) fn apply_con_ty(
    con_ty: &Ty,
    args: &Vec<ast::Named<Ty>>,
    cons: &ScopeMap<Id, TyCon>,
    var_gen: &mut TyVarGen,
    level: u32,
    loc: &ast::Loc,
    ignore_extra: bool,
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
                FunArgs::Positional(con_ty_args) => {
                    if (!ignore_extra && con_ty_args.len() != args.len())
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
                        unify(ty1, &ty2.node, cons, var_gen, level, loc);
                    }
                }

                FunArgs::Named(con_ty_args) => {
                    let mut arg_names: Set<&Id> = Default::default();

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
                        if con_ty_args.get(name).is_none() {
                            panic!(
                                "{}: Constructor doesn't take named argument '{}'",
                                loc_display(loc),
                                name,
                            );
                        }
                        if !arg_names.insert(name) {
                            panic!(
                                "{}: Named argument '{}' applied multiple times",
                                loc_display(loc),
                                name,
                            );
                        }
                    }

                    let con_ty_arg_names: Set<&Id> = con_ty_args.keys().collect();
                    if !ignore_extra && con_ty_arg_names != arg_names {
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

                    for ast::Named { name, node } in args {
                        let name = match name.as_ref() {
                            Some(name) => name,
                            None => {
                                panic!(
                                    "{}: Constructor takes named arguments, but applied positional argument",
                                    loc_display(loc)
                                );
                            }
                        };
                        let ty1 = con_ty_args.get(name).unwrap();
                        unify(ty1, node, cons, var_gen, level, loc);
                    }
                }
            }

            (**con_ty_ret).clone()
        }

        Ty::Con(_, _) => {
            if args.is_empty() {
                return con_ty.clone();
            }
            panic!(
                "{}: Constructor doesn't take arguments, but applied {} arguments",
                loc_display(loc),
                args.len(),
            );
        }

        Ty::Var(_) | Ty::App(_, _, _) | Ty::Anonymous { .. } | Ty::QVar(_, _) => {
            if args.is_empty() {
                return con_ty.clone();
            }
            panic!(
                "{}: BUG: ty = {:?}, args = {:?}",
                loc_display(loc),
                con_ty,
                args
            )
        }
    }
}
