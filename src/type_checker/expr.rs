use crate::ast::{self, Id};
use crate::collections::*;
use crate::interpolation::StrPart;
use crate::type_checker::convert::convert_ast_ty;
use crate::type_checker::pat::check_pat;
use crate::type_checker::stmt::check_stmts;
use crate::type_checker::ty::*;
use crate::type_checker::unification::{try_unify_one_way, unify, unify_expected_ty};
use crate::type_checker::{TcFunState, loc_display};

use std::mem::{replace, take};

use smol_str::SmolStr;

/// Returns the type of the expression, and binders that the expression binds.
///
/// Only boolean expressions bind variables.
///
/// - `<expr> is <pat>` binds the variables that `<pat>` binds.
///
/// - `<expr1> and <expr2>` binds the variables that `<expr1>` and `<expr2>` bind.
///   `<expr1>` and `<expr2>` need to bind disjoint set of variables.
///
/// Other expressions don't bind any variables.
///
/// Variables bound in `if` and `while` conditionals are used in the bodies.
pub(super) fn check_expr(
    tc_state: &mut TcFunState,
    expr: &mut ast::L<ast::Expr>,
    expected_ty: Option<&Ty>,
    level: u32,
    loop_stack: &mut Vec<Option<Id>>,
) -> (Ty, Map<Id, Ty>) {
    let loc = expr.loc.clone();

    match &mut expr.node {
        ast::Expr::Var(ast::VarExpr {
            id: var,
            user_ty_args,
            ty_args,
        }) => {
            assert!(ty_args.is_empty());

            // Check if local.
            if let Some(ty) = tc_state.env.get(var) {
                if !user_ty_args.is_empty() {
                    panic!(
                        "{}: Local variables can't have type parameters, but `{}` is passed type arguments",
                        loc_display(&expr.loc),
                        var
                    );
                }
                return (
                    unify_expected_ty(
                        ty.clone(),
                        expected_ty,
                        tc_state.tys.tys.cons(),
                        tc_state.var_gen,
                        level,
                        &expr.loc,
                    ),
                    Default::default(),
                );
            }

            let scheme = match tc_state.tys.top_schemes.get(var) {
                Some(scheme) => scheme,
                None => panic!("{}: Unbound variable {}", loc_display(&expr.loc), var),
            };

            let ty = if user_ty_args.is_empty() {
                let (ty, ty_args) =
                    scheme.instantiate(level, tc_state.var_gen, tc_state.preds, &expr.loc);

                expr.node = ast::Expr::Var(ast::VarExpr {
                    id: var.clone(),
                    user_ty_args: vec![],
                    ty_args: ty_args.into_iter().map(Ty::Var).collect(),
                });

                ty
            } else {
                if scheme.quantified_vars.len() != user_ty_args.len() {
                    panic!(
                        "{}: Variable {} takes {} type arguments, but applied to {}",
                        loc_display(&expr.loc),
                        var,
                        scheme.quantified_vars.len(),
                        user_ty_args.len()
                    );
                }

                let user_ty_args_converted: Vec<Ty> = user_ty_args
                    .iter()
                    .map(|ty| convert_ast_ty(&tc_state.tys.tys, &ty.node, &ty.loc))
                    .collect();

                let ty =
                    scheme.instantiate_with_tys(&user_ty_args_converted, tc_state.preds, &expr.loc);

                expr.node = ast::Expr::Var(ast::VarExpr {
                    id: var.clone(),
                    user_ty_args: vec![],
                    ty_args: user_ty_args_converted,
                });

                ty
            };

            (
                unify_expected_ty(
                    ty,
                    expected_ty,
                    tc_state.tys.tys.cons(),
                    tc_state.var_gen,
                    level,
                    &expr.loc,
                ),
                Default::default(),
            )
        }

        // <object:Expr>.<field:Id>.
        // This updates the expression as `MethodSelect` if the `field` turns out to be a method.
        ast::Expr::FieldSelect(ast::FieldSelectExpr {
            object,
            field,
            user_ty_args,
        }) => {
            let ty = {
                let (object_ty, _) = check_expr(tc_state, object, None, level, loop_stack);

                let ty_normalized = object_ty.normalize(tc_state.tys.tys.cons());
                match &ty_normalized {
                    Ty::Anonymous {
                        labels,
                        extension,
                        kind: RecordOrVariant::Record,
                        ..
                    } => {
                        if !user_ty_args.is_empty() {
                            panic!(
                                "{}: Record field with type arguments",
                                loc_display(&expr.loc),
                            );
                        }
                        let (labels, _) = crate::type_checker::row_utils::collect_rows(
                            tc_state.tys.tys.cons(),
                            &ty_normalized,
                            RecordOrVariant::Record,
                            labels,
                            extension.clone(),
                        );
                        match labels.get(field) {
                            Some(field_ty) => field_ty.clone(),
                            None => panic!(
                                "{}: Record with fields {:?} does not have field {}",
                                loc_display(&object.loc),
                                labels.keys().collect::<Vec<_>>(),
                                field
                            ),
                        }
                    }

                    other => {
                        let (ty, new_expr) = check_field_select(
                            tc_state,
                            object,
                            field,
                            user_ty_args,
                            other,
                            &expr.loc,
                            level,
                        );
                        expr.node = new_expr;
                        ty
                    }
                }
            };
            (
                unify_expected_ty(
                    ty,
                    expected_ty,
                    tc_state.tys.tys.cons(),
                    tc_state.var_gen,
                    level,
                    &expr.loc,
                ),
                Default::default(),
            )
        }

        ast::Expr::MethodSelect(_) => panic!("MethodSelect in type checker"),

        ast::Expr::ConstrSelect(ast::Constructor {
            variant,
            ty,
            constr,
            user_ty_args,
            ty_args,
        }) => {
            assert!(ty_args.is_empty());

            let scheme = match constr {
                Some(constr) => tc_state
                    .tys
                    .associated_fn_schemes
                    .get(ty)
                    .unwrap_or_else(|| {
                        panic!(
                            "{}: Type {} is not in type environment",
                            loc_display(&expr.loc),
                            ty
                        )
                    })
                    .get(constr)
                    .unwrap_or_else(|| {
                        panic!(
                            "{}: Type {} does not have the constructor {}",
                            loc_display(&expr.loc),
                            ty,
                            constr
                        )
                    }),
                None => tc_state.tys.top_schemes.get(ty).unwrap_or_else(|| {
                    panic!("{}: Unknown constructor {}", loc_display(&expr.loc), ty)
                }),
            };

            let variant = *variant;

            let con_ty = if user_ty_args.is_empty() {
                let (con_ty, con_ty_args) =
                    scheme.instantiate(level, tc_state.var_gen, tc_state.preds, &expr.loc);

                expr.node = ast::Expr::ConstrSelect(ast::Constructor {
                    variant,
                    ty: ty.clone(),
                    constr: constr.clone(),
                    user_ty_args: vec![],
                    ty_args: con_ty_args.into_iter().map(Ty::Var).collect(),
                });

                if variant {
                    make_variant(tc_state, con_ty, level, &loc)
                } else {
                    con_ty
                }
            } else {
                if scheme.quantified_vars.len() != user_ty_args.len() {
                    panic!(
                        "{}: Constructor {}{}{} takes {} type arguments, but applied to {}",
                        loc_display(&expr.loc),
                        ty,
                        if constr.is_some() { "." } else { "" },
                        constr.as_ref().cloned().unwrap_or(SmolStr::new_static("")),
                        scheme.quantified_vars.len(),
                        user_ty_args.len()
                    );
                }

                let user_ty_args_converted: Vec<Ty> = user_ty_args
                    .iter()
                    .map(|ty| convert_ast_ty(&tc_state.tys.tys, &ty.node, &ty.loc))
                    .collect();

                let con_ty =
                    scheme.instantiate_with_tys(&user_ty_args_converted, tc_state.preds, &expr.loc);

                expr.node = ast::Expr::ConstrSelect(ast::Constructor {
                    variant,
                    ty: ty.clone(),
                    constr: constr.clone(),
                    user_ty_args: vec![],
                    ty_args: user_ty_args_converted,
                });

                if variant {
                    make_variant(tc_state, con_ty, level, &loc)
                } else {
                    con_ty
                }
            };

            (
                unify_expected_ty(
                    con_ty,
                    expected_ty,
                    tc_state.tys.tys.cons(),
                    tc_state.var_gen,
                    level,
                    &expr.loc,
                ),
                Default::default(),
            )
        }

        ast::Expr::AssocFnSelect(ast::AssocFnSelectExpr {
            ty,
            ty_user_ty_args,
            member,
            user_ty_args,
            ty_args,
        }) => {
            assert!(ty_args.is_empty());

            if !ty_user_ty_args.is_empty() {
                let con =
                    tc_state.tys.tys.get_con(ty).unwrap_or_else(|| {
                        panic!("{}: Unknown type {}", loc_display(&expr.loc), ty)
                    });

                if con.ty_params.len() != ty_user_ty_args.len() {
                    panic!(
                        "{}: Type {} takes {} type arguments, but applied to {}",
                        loc_display(&expr.loc),
                        ty,
                        con.ty_params.len(),
                        ty_user_ty_args.len(),
                    );
                }
            }

            let scheme = tc_state
                .tys
                .associated_fn_schemes
                .get(ty)
                .unwrap_or_else(|| panic!("{}: Unknown type {}", loc_display(&expr.loc), ty))
                .get(member)
                .unwrap_or_else(|| {
                    panic!(
                        "{}: Type {} does not have associated function {}",
                        loc_display(&expr.loc),
                        ty,
                        member
                    )
                });

            let ty_user_ty_args_converted: Vec<Ty> = ty_user_ty_args
                .iter()
                .map(|ty| convert_ast_ty(&tc_state.tys.tys, &ty.node, &ty.loc))
                .collect();

            let user_ty_args_converted: Vec<Ty> = user_ty_args
                .iter()
                .map(|ty| convert_ast_ty(&tc_state.tys.tys, &ty.node, &ty.loc))
                .collect();

            for (ty_ty_arg, method_ty_arg) in ty_user_ty_args_converted
                .iter()
                .zip(user_ty_args_converted.iter())
            {
                unify(
                    ty_ty_arg,
                    method_ty_arg,
                    tc_state.tys.tys.cons(),
                    tc_state.var_gen,
                    level,
                    &expr.loc,
                );
            }

            let method_ty = if user_ty_args_converted.is_empty() {
                let (method_ty, method_ty_args) =
                    scheme.instantiate(level, tc_state.var_gen, tc_state.preds, &expr.loc);

                for (ty_ty_arg, method_ty_arg) in
                    ty_user_ty_args_converted.iter().zip(method_ty_args.iter())
                {
                    unify(
                        ty_ty_arg,
                        &Ty::Var(method_ty_arg.clone()),
                        tc_state.tys.tys.cons(),
                        tc_state.var_gen,
                        level,
                        &expr.loc,
                    );
                }

                expr.node = ast::Expr::AssocFnSelect(ast::AssocFnSelectExpr {
                    ty: ty.clone(),
                    ty_user_ty_args: vec![],
                    member: member.clone(),
                    user_ty_args: vec![],
                    ty_args: method_ty_args.into_iter().map(Ty::Var).collect(),
                });

                method_ty
            } else {
                if scheme.quantified_vars.len() != user_ty_args.len() {
                    panic!(
                        "{}: Associated function {}.{} takes {} type arguments, but applied to {}",
                        loc_display(&expr.loc),
                        ty,
                        member,
                        scheme.quantified_vars.len(),
                        user_ty_args.len()
                    );
                }

                let method_ty =
                    scheme.instantiate_with_tys(&user_ty_args_converted, tc_state.preds, &expr.loc);

                expr.node = ast::Expr::AssocFnSelect(ast::AssocFnSelectExpr {
                    ty: ty.clone(),
                    ty_user_ty_args: vec![],
                    member: member.clone(),
                    user_ty_args: vec![],
                    ty_args: user_ty_args_converted,
                });

                method_ty
            };

            (
                unify_expected_ty(
                    method_ty,
                    expected_ty,
                    tc_state.tys.tys.cons(),
                    tc_state.var_gen,
                    level,
                    &expr.loc,
                ),
                Default::default(),
            )
        }

        ast::Expr::Call(ast::CallExpr { fun, args }) => {
            let (fun_ty, _) = check_expr(tc_state, fun, None, level, loop_stack);

            match fun_ty.normalize(tc_state.tys.tys.cons()) {
                Ty::Fun {
                    args: param_tys,
                    ret: ret_ty,
                    exceptions,
                } => {
                    if param_tys.len() != args.len() {
                        panic!(
                            "{}: Function with arity {} is passed {} args",
                            loc_display(&expr.loc),
                            param_tys.len(),
                            args.len()
                        );
                    }

                    let ret_ty = unify_expected_ty(
                        *ret_ty,
                        expected_ty,
                        tc_state.tys.tys.cons(),
                        tc_state.var_gen,
                        level,
                        &expr.loc,
                    );

                    match param_tys {
                        FunArgs::Positional(param_tys) => {
                            for arg in args.iter() {
                                if arg.name.is_some() {
                                    panic!(
                                        "{}: Named argument applied to function that expects positional arguments",
                                        loc_display(&expr.loc),
                                    );
                                }
                            }

                            let mut arg_tys: Vec<Ty> = Vec::with_capacity(args.len());
                            for (param_ty, arg) in param_tys.iter().zip(args.iter_mut()) {
                                let (arg_ty, _) = check_expr(
                                    tc_state,
                                    &mut arg.expr,
                                    Some(param_ty),
                                    level,
                                    loop_stack,
                                );
                                arg_tys.push(arg_ty);
                            }
                        }

                        FunArgs::Named(param_tys) => {
                            for arg in args.iter_mut() {
                                if arg.name.is_none() {
                                    match &arg.expr.node {
                                        ast::Expr::Var(ast::VarExpr {
                                            id,
                                            user_ty_args: _,
                                            ty_args: _,
                                        }) => {
                                            arg.name = Some(id.clone());
                                        }
                                        _ => {
                                            panic!(
                                                "{}: Positional argument applied to function that expects named arguments",
                                                loc_display(&expr.loc),
                                            );
                                        }
                                    }
                                }
                            }

                            let param_names: Set<&Id> = param_tys.keys().collect();
                            let arg_names: Set<&Id> =
                                args.iter().map(|arg| arg.name.as_ref().unwrap()).collect();

                            if param_names != arg_names {
                                panic!(
                                    "{}: Function expects arguments with names {:?}, but passed {:?}",
                                    loc_display(&expr.loc),
                                    param_names,
                                    arg_names
                                );
                            }

                            for arg in args {
                                let arg_name: &Id = arg.name.as_ref().unwrap();
                                let param_ty: &Ty = param_tys.get(arg_name).unwrap();
                                let (arg_ty, _) = check_expr(
                                    tc_state,
                                    &mut arg.expr,
                                    Some(param_ty),
                                    level,
                                    loop_stack,
                                );
                                unify(
                                    &arg_ty,
                                    param_ty,
                                    tc_state.tys.tys.cons(),
                                    tc_state.var_gen,
                                    level,
                                    &expr.loc,
                                );
                            }
                        }
                    }

                    if let Some(exn) = &exceptions {
                        unify(
                            exn,
                            &tc_state.exceptions,
                            tc_state.tys.tys.cons(),
                            tc_state.var_gen,
                            level,
                            &expr.loc,
                        );
                    }

                    (ret_ty, Default::default())
                }

                _ => panic!(
                    "{}: Function in function application is not a function: {:?}",
                    loc_display(&expr.loc),
                    fun_ty,
                ),
            }
        }

        ast::Expr::Int(ast::IntExpr {
            text,
            suffix,
            radix,
            parsed,
        }) => {
            let kind: ast::IntKind = suffix.unwrap_or_else(|| {
                match expected_ty.map(|ty| ty.normalize(tc_state.tys.tys.cons())) {
                    Some(Ty::Con(con, _kind)) if con == "I8" => ast::IntKind::I8,
                    Some(Ty::Con(con, _kind)) if con == "U8" => ast::IntKind::U8,
                    Some(Ty::Con(con, _kind)) if con == "I32" => ast::IntKind::I32,
                    Some(Ty::Con(con, _kind)) if con == "U32" => ast::IntKind::U32,

                    None | Some(Ty::Var(_)) => {
                        // Try defaulting as i32.
                        ast::IntKind::I32
                    }

                    Some(other) => panic!(
                        "{}: Expected {}, found integer literal",
                        loc_display(&expr.loc),
                        other,
                    ),
                }
            });

            *suffix = Some(kind);

            match kind {
                ast::IntKind::I8 => {
                    *parsed = i8::from_str_radix(text, *radix).unwrap_or_else(|err| {
                        panic!(
                            "{}: Integer cannot be parsed as I8: {:?}",
                            loc_display(&expr.loc),
                            err
                        )
                    }) as u8 as u64;
                    (
                        unify_expected_ty(
                            Ty::Con("I8".into(), Kind::Star),
                            expected_ty,
                            tc_state.tys.tys.cons(),
                            tc_state.var_gen,
                            level,
                            &expr.loc,
                        ),
                        Default::default(),
                    )
                }

                ast::IntKind::U8 => {
                    *parsed = u8::from_str_radix(text, *radix).unwrap_or_else(|err| {
                        panic!(
                            "{}: Integer cannot be parsed as U8: {:?}",
                            loc_display(&expr.loc),
                            err
                        )
                    }) as u64;
                    (
                        unify_expected_ty(
                            Ty::Con("U8".into(), Kind::Star),
                            expected_ty,
                            tc_state.tys.tys.cons(),
                            tc_state.var_gen,
                            level,
                            &expr.loc,
                        ),
                        Default::default(),
                    )
                }

                ast::IntKind::I32 => {
                    *parsed = i32::from_str_radix(text, *radix).unwrap_or_else(|err| {
                        panic!(
                            "{}: Integer cannot be parsed as I32: {:?}",
                            loc_display(&expr.loc),
                            err
                        )
                    }) as u32 as u64;
                    (
                        unify_expected_ty(
                            Ty::Con("I32".into(), Kind::Star),
                            expected_ty,
                            tc_state.tys.tys.cons(),
                            tc_state.var_gen,
                            level,
                            &expr.loc,
                        ),
                        Default::default(),
                    )
                }

                ast::IntKind::U32 => {
                    *parsed = u32::from_str_radix(text, *radix).unwrap_or_else(|err| {
                        panic!(
                            "{}: Integer cannot be parsed as U32: {:?}",
                            loc_display(&expr.loc),
                            err
                        )
                    }) as u64;
                    (
                        unify_expected_ty(
                            Ty::Con("U32".into(), Kind::Star),
                            expected_ty,
                            tc_state.tys.tys.cons(),
                            tc_state.var_gen,
                            level,
                            &expr.loc,
                        ),
                        Default::default(),
                    )
                }
            }
        }

        ast::Expr::Str(parts) => {
            for part in parts {
                match part {
                    StrPart::Str(_) => continue,
                    StrPart::Expr(expr) => {
                        let expr_var =
                            tc_state
                                .var_gen
                                .new_var(level, Kind::Star, expr.loc.clone());
                        tc_state.preds.push(Pred {
                            trait_: Ty::to_str_id(),
                            params: vec![Ty::Var(expr_var.clone())],
                            loc: expr.loc.clone(),
                        });
                        let (part_ty, _) =
                            check_expr(tc_state, expr, Some(&Ty::Var(expr_var)), level, loop_stack);
                        let expr_node = replace(&mut expr.node, ast::Expr::Self_);
                        expr.node = ast::Expr::Call(ast::CallExpr {
                            fun: Box::new(ast::L {
                                node: ast::Expr::MethodSelect(ast::MethodSelectExpr {
                                    object: Box::new(ast::L {
                                        node: expr_node,
                                        loc: expr.loc.clone(),
                                    }),
                                    object_ty: Some(part_ty.clone()),
                                    method_ty_id: SmolStr::new_static("ToStr"),
                                    method: SmolStr::new_static("toStr"),
                                    ty_args: vec![part_ty, tc_state.exceptions.clone()],
                                }),
                                loc: expr.loc.clone(),
                            }),
                            args: vec![],
                        });
                    }
                }
            }

            (
                unify_expected_ty(
                    Ty::str(),
                    expected_ty,
                    tc_state.tys.tys.cons(),
                    tc_state.var_gen,
                    level,
                    &expr.loc,
                ),
                Default::default(),
            )
        }

        ast::Expr::Char(_) => (
            unify_expected_ty(
                Ty::char(),
                expected_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                &expr.loc,
            ),
            Default::default(),
        ),

        ast::Expr::Self_ => match tc_state.env.get("self") {
            Some(self_ty) => (
                unify_expected_ty(
                    self_ty.clone(),
                    expected_ty,
                    tc_state.tys.tys.cons(),
                    tc_state.var_gen,
                    level,
                    &expr.loc,
                ),
                Default::default(),
            ),
            None => panic!("{}: Unbound self", loc_display(&expr.loc)),
        },

        ast::Expr::BinOp(ast::BinOpExpr { left, right, op }) => {
            let method = match op {
                ast::BinOp::And => {
                    let bool_ty = Ty::Con("Bool".into(), Kind::Star);
                    let (_, mut left_binders) =
                        check_expr(tc_state, left, Some(&bool_ty), level, loop_stack);
                    tc_state.env.enter();
                    left_binders.iter().for_each(|(k, v)| {
                        tc_state.env.insert(k.clone(), v.clone());
                    });
                    let (_, right_binders) =
                        check_expr(tc_state, right, Some(&bool_ty), level, loop_stack);
                    tc_state.env.exit();

                    let left_binder_vars: Set<&Id> = left_binders.keys().collect();
                    let right_binder_vars: Set<&Id> = right_binders.keys().collect();
                    if !left_binder_vars.is_disjoint(&right_binder_vars) {
                        let intersection: Vec<Id> = left_binder_vars
                            .intersection(&right_binder_vars)
                            .map(|id| (**id).clone())
                            .collect();
                        panic!(
                            "{}: Left and right exprs in `and` bind same variables: {}",
                            loc_display(&expr.loc),
                            intersection.join(", "),
                        );
                    }

                    left_binders.extend(right_binders);
                    return (bool_ty, left_binders);
                }

                ast::BinOp::Or => {
                    let bool_ty = Ty::Con("Bool".into(), Kind::Star);
                    check_expr(tc_state, left, Some(&bool_ty), level, loop_stack);
                    check_expr(tc_state, right, Some(&bool_ty), level, loop_stack);
                    return (bool_ty, Default::default());
                }

                ast::BinOp::Add => "__add",
                ast::BinOp::Subtract => "__sub",
                ast::BinOp::Equal => "__eq",
                ast::BinOp::NotEqual => "__neq",
                ast::BinOp::Multiply => "__mul",
                ast::BinOp::Divide => "__div",
                ast::BinOp::Lt => "__lt",
                ast::BinOp::Gt => "__gt",
                ast::BinOp::LtEq => "__le",
                ast::BinOp::GtEq => "__ge",
                ast::BinOp::BitOr => "__bitor",
                ast::BinOp::BitAnd => "__bitand",
                ast::BinOp::LeftShift => "__shl",
                ast::BinOp::RightShift => "__shr",
            };

            let desugared = ast::L {
                loc: expr.loc.clone(),
                node: ast::Expr::Call(ast::CallExpr {
                    fun: Box::new(ast::L {
                        loc: left.loc.clone(),
                        node: ast::Expr::FieldSelect(ast::FieldSelectExpr {
                            object: left.clone(),
                            field: SmolStr::new_static(method),
                            user_ty_args: vec![],
                        }),
                    }),
                    args: vec![ast::CallArg {
                        name: None,
                        expr: (**right).clone(),
                    }],
                }),
            };

            *expr = desugared;

            check_expr(tc_state, expr, expected_ty, level, loop_stack)
        }

        ast::Expr::UnOp(ast::UnOpExpr { op, expr: arg }) => match op {
            ast::UnOp::Not => {
                let (ty, _) = check_expr(tc_state, arg, Some(&Ty::bool()), level, loop_stack);
                let desugared = ast::L {
                    loc: expr.loc.clone(),
                    node: ast::Expr::Call(ast::CallExpr {
                        fun: Box::new(ast::L {
                            loc: arg.loc.clone(),
                            node: ast::Expr::MethodSelect(ast::MethodSelectExpr {
                                object: arg.clone(),
                                object_ty: Some(Ty::bool()),
                                method_ty_id: SmolStr::new_static("Bool"),
                                ty_args: vec![],
                                method: SmolStr::new_static("__not"),
                            }),
                        }),
                        args: vec![],
                    }),
                };
                *expr = desugared;
                (ty, Default::default())
            }

            ast::UnOp::Neg => {
                let desugared = ast::L {
                    loc: expr.loc.clone(),
                    node: ast::Expr::Call(ast::CallExpr {
                        fun: Box::new(ast::L {
                            loc: arg.loc.clone(),
                            node: ast::Expr::FieldSelect(ast::FieldSelectExpr {
                                object: arg.clone(),
                                field: SmolStr::new_static("__neg"),
                                user_ty_args: vec![],
                            }),
                        }),
                        args: vec![],
                    }),
                };

                *expr = desugared;

                check_expr(tc_state, expr, expected_ty, level, loop_stack)
            }
        },

        ast::Expr::Record(fields) => {
            if fields.is_empty() {
                return (
                    unify_expected_ty(
                        Ty::unit(),
                        expected_ty,
                        tc_state.tys.tys.cons(),
                        tc_state.var_gen,
                        level,
                        &expr.loc,
                    ),
                    Default::default(),
                );
            }

            // TODO: For now only supporting named fields.
            let mut field_names: Set<&Id> = Default::default();
            for field in fields.iter() {
                match &field.name {
                    Some(name) => {
                        if !field_names.insert(name) {
                            panic!(
                                "{}: Field name {} occurs multiple times in the record",
                                loc_display(&expr.loc),
                                name
                            );
                        }
                    }
                    None => panic!("{}: Unnamed record field", loc_display(&expr.loc)),
                }
            }

            // To give better error messages use the field types in the expected type as expected
            // types of the expr fields when possible.
            let expected_fields = expected_ty.and_then(|expected_ty| {
                match expected_ty.normalize(tc_state.tys.tys.cons()) {
                    Ty::Anonymous {
                        labels: expected_fields,
                        extension: _,
                        kind: RecordOrVariant::Record,
                        is_row: _,
                    } => Some(expected_fields),
                    _ => None,
                }
            });

            let mut record_fields: TreeMap<Id, Ty> = TreeMap::new();
            for field in fields.iter_mut() {
                let field_name = field.name.as_ref().unwrap();
                let expected_ty = expected_fields
                    .as_ref()
                    .and_then(|expected_fields| expected_fields.get(field_name));
                let (field_ty, _) =
                    check_expr(tc_state, &mut field.node, expected_ty, level, loop_stack);
                record_fields.insert(field_name.clone(), field_ty);
            }

            (
                unify_expected_ty(
                    Ty::Anonymous {
                        labels: record_fields,
                        extension: None,
                        kind: RecordOrVariant::Record,
                        is_row: false,
                    },
                    expected_ty,
                    tc_state.tys.tys.cons(),
                    tc_state.var_gen,
                    level,
                    &expr.loc,
                ),
                Default::default(),
            )
        }

        ast::Expr::Return(expr) => {
            let return_ty = tc_state.return_ty.clone();
            check_expr(tc_state, expr, Some(&return_ty), level, loop_stack);
            (
                expected_ty.cloned().unwrap_or_else(|| {
                    Ty::Var(
                        tc_state
                            .var_gen
                            .new_var(level, Kind::Star, expr.loc.clone()),
                    )
                }),
                Default::default(),
            )
        }

        ast::Expr::Match(match_expr) => {
            let mut rhs_tys = check_match_expr(
                tc_state,
                match_expr,
                &expr.loc,
                expected_ty,
                level,
                loop_stack,
            );

            // Unify RHS types. When the `expected_ty` is available this doesn't do anything.
            // Otherwise this checks that all branches return the same type.
            // We could do this only when `expected_ty` is not available, but it shouldn't hurt to
            // do it always.
            for rhs_tys in rhs_tys.windows(2) {
                unify(
                    &rhs_tys[0],
                    &rhs_tys[1],
                    tc_state.tys.tys.cons(),
                    tc_state.var_gen,
                    level,
                    &expr.loc,
                );
            }

            // Same as above, only useful when `expected_ty` is not available.
            (
                unify_expected_ty(
                    rhs_tys.pop().unwrap(),
                    expected_ty,
                    tc_state.tys.tys.cons(),
                    tc_state.var_gen,
                    level,
                    &expr.loc,
                ),
                Default::default(),
            )
        }

        ast::Expr::If(if_expr) => {
            let mut branch_tys: Vec<Ty> =
                check_if_expr(tc_state, if_expr, expected_ty, level, loop_stack);

            // When expected type is available, unify with it for better errors.
            match expected_ty {
                Some(expected_ty) => {
                    for ty in &branch_tys {
                        unify(
                            ty,
                            expected_ty,
                            tc_state.tys.tys.cons(),
                            tc_state.var_gen,
                            level,
                            &expr.loc,
                        );
                    }
                }
                None => {
                    for ty_pair in branch_tys.windows(2) {
                        unify(
                            &ty_pair[0],
                            &ty_pair[1],
                            tc_state.tys.tys.cons(),
                            tc_state.var_gen,
                            level,
                            &expr.loc,
                        );
                    }
                }
            }

            (branch_tys.pop().unwrap(), Default::default())
        }

        ast::Expr::Fn(ast::FnExpr {
            sig,
            body,
            idx,
            inferred_ty,
        }) => {
            assert!(sig.context.type_params.is_empty());
            assert!(sig.context.preds.is_empty());
            assert!(matches!(&sig.self_, ast::SelfParam::No));
            assert_eq!(*idx, 0);
            assert!(inferred_ty.is_none());

            let (expected_args, expected_ret, expected_exceptions) = match expected_ty {
                Some(expected_ty) => match expected_ty.normalize(tc_state.tys.tys.cons()) {
                    Ty::Fun {
                        args,
                        ret,
                        exceptions,
                    } => (Some(args), Some(ret), Some(exceptions)),

                    Ty::Con(_, _)
                    | Ty::Var(_)
                    | Ty::App(_, _, _)
                    | Ty::QVar(_, _)
                    | Ty::Anonymous { .. } => (None, None, None),
                },
                None => (None, None, None),
            };

            tc_state.env.enter(); // for term params

            let ret_ty = match &sig.return_ty {
                Some(ty) => convert_ast_ty(&tc_state.tys.tys, &ty.node, &ty.loc),
                None => match expected_ret {
                    Some(ret) => (*ret).clone(),
                    None => Ty::Var(tc_state.var_gen.new_var(
                        level + 1,
                        Kind::Star,
                        expr.loc.clone(),
                    )),
                },
            };

            let exceptions = match &sig.exceptions {
                Some(exc) => convert_ast_ty(&tc_state.tys.tys, &exc.node, &exc.loc),
                None => match expected_exceptions {
                    Some(Some(exn)) => (*exn).clone(),
                    _ => Ty::Var(
                        tc_state
                            .var_gen
                            .new_var(level + 1, Kind::Star, expr.loc.clone()),
                    ),
                },
            };

            let mut param_tys: Vec<Ty> = Vec::with_capacity(sig.params.len());
            for (param_idx, (param_name, param_ty)) in sig.params.iter().enumerate() {
                let param_ty_converted: Option<Ty> = param_ty
                    .as_ref()
                    .map(|param_ty| convert_ast_ty(&tc_state.tys.tys, &param_ty.node, &expr.loc));

                let param_ty_converted: Ty = param_ty_converted.unwrap_or_else(|| {
                    expected_args
                        .as_ref()
                        .and_then(|expected_args| match expected_args {
                            FunArgs::Positional(expected_args) => {
                                expected_args.get(param_idx).cloned()
                            }
                            FunArgs::Named(_) => None,
                        })
                        .unwrap_or_else(|| {
                            panic!(
                                "{}: fn expr needs argument type annotations",
                                loc_display(&expr.loc)
                            )
                        })
                });

                tc_state
                    .env
                    .insert(param_name.clone(), param_ty_converted.clone());
                param_tys.push(param_ty_converted.clone());
            }

            let old_ret_ty = replace(&mut tc_state.return_ty, ret_ty.clone());
            let old_exceptions = replace(&mut tc_state.exceptions, exceptions.clone());
            let old_preds = take(tc_state.preds);

            check_stmts(tc_state, body, Some(&ret_ty), 0, &mut Vec::new());

            let new_preds: Vec<Pred> = replace(tc_state.preds, old_preds);
            crate::type_checker::resolve_preds(
                tc_state.trait_env,
                tc_state.assumps,
                tc_state.tys,
                new_preds,
                tc_state.var_gen,
                0,
            );

            let exceptions = replace(&mut tc_state.exceptions, old_exceptions);
            let ret_ty = replace(&mut tc_state.return_ty, old_ret_ty);

            tc_state.env.exit();

            let ty = Ty::Fun {
                args: FunArgs::Positional(param_tys),
                ret: Box::new(ret_ty),
                exceptions: Some(Box::new(exceptions)),
            };

            let ty = unify_expected_ty(
                ty,
                expected_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                &expr.loc,
            );
            *inferred_ty = Some(ty.clone());
            (ty, Default::default())
        }

        ast::Expr::Is(ast::IsExpr { expr, pat }) => {
            let (expr_ty, _) = check_expr(tc_state, expr, None, level, loop_stack);
            tc_state.env.enter();
            let pat_ty = check_pat(tc_state, pat, level);
            let pat_binders: Map<Id, Ty> = tc_state.env.exit();
            unify(
                &pat_ty,
                &expr_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                &pat.loc,
            );
            (Ty::bool(), pat_binders)
        }

        ast::Expr::Do(stmts) => {
            tc_state.env.enter();
            let ty = check_stmts(tc_state, stmts, expected_ty, level, loop_stack);
            tc_state.env.exit();
            (ty, Default::default())
        }

        ast::Expr::Seq { ty, elems } => {
            /*
            Functions used in the desugaring:

            - empty:    [?exn] Fn() Empty / ?exn
            - once:     [t, ?exn] Fn(t) Once[t] / ?exn
            - onceWith: [exn, t, ?exn] Fn(Fn() : t / exn) OnceWith[t, exn] / ?exn
            - chain:    [iter, item, exn, other, ?exn] [Iterator[iter, item, exn]] Fn(iter, other) Chain[iter, other, item, exn] / ?exn
            */

            let iter_ty = ty.clone();

            let iter_expr = if elems.is_empty() {
                ast::L {
                    loc: loc.clone(),
                    node: ast::Expr::Call(ast::CallExpr {
                        fun: Box::new(ast::L {
                            loc: loc.clone(),
                            node: ast::Expr::Var(ast::VarExpr {
                                id: SmolStr::new("empty"),
                                user_ty_args: vec![],
                                ty_args: vec![],
                            }),
                        }),
                        args: vec![],
                    }),
                }
            } else {
                let mut pairs = false;
                let mut singles = false;

                for (k, _) in elems.iter() {
                    match k {
                        Some(_) => pairs = true,
                        None => singles = true,
                    }
                }

                if pairs && singles {
                    panic!(
                        "{}: Sequence has both key-value pair and single element",
                        loc_display(&expr.loc)
                    );
                }

                let mut elem_iters: Vec<ast::L<ast::Expr>> = Vec::with_capacity(elems.len());
                for (k, v) in elems.iter() {
                    let elem = match k {
                        Some(k) => ast::L {
                            loc: loc.clone(),
                            node: ast::Expr::Record(vec![
                                ast::Named {
                                    name: Some(SmolStr::new("key")),
                                    node: k.clone(),
                                },
                                ast::Named {
                                    name: Some(SmolStr::new("value")),
                                    node: v.clone(),
                                },
                            ]),
                        },
                        None => v.clone(),
                    };
                    elem_iters.push(ast::L {
                        loc: loc.clone(),
                        node: ast::Expr::Call(ast::CallExpr {
                            fun: Box::new(ast::L {
                                loc: loc.clone(),
                                node: ast::Expr::Var(ast::VarExpr {
                                    id: SmolStr::new_static("once"),
                                    user_ty_args: vec![],
                                    ty_args: vec![],
                                }),
                            }),
                            args: vec![ast::CallArg {
                                name: None,
                                expr: elem,
                            }],
                        }),
                    });
                }

                let mut iter = elem_iters.into_iter();
                let init = iter.next().unwrap();
                iter.fold(init, |elem, next| ast::L {
                    loc: loc.clone(),
                    node: ast::Expr::Call(ast::CallExpr {
                        fun: Box::new(ast::L {
                            loc: loc.clone(),
                            node: ast::Expr::FieldSelect(ast::FieldSelectExpr {
                                object: Box::new(elem),
                                field: SmolStr::new_static("chain"),
                                user_ty_args: vec![],
                            }),
                        }),
                        args: vec![ast::CallArg {
                            name: None,
                            expr: next,
                        }],
                    }),
                })
            };

            let desugared = match iter_ty {
                Some(iter_ty) => {
                    let field_select_expr = ast::L {
                        loc: loc.clone(),
                        node: ast::Expr::AssocFnSelect(ast::AssocFnSelectExpr {
                            ty: iter_ty,
                            ty_user_ty_args: vec![],
                            member: SmolStr::new_static("fromIter"),
                            user_ty_args: vec![],
                            ty_args: vec![],
                        }),
                    };

                    ast::L {
                        loc: loc.clone(),
                        node: ast::Expr::Call(ast::CallExpr {
                            fun: Box::new(field_select_expr),
                            args: vec![ast::CallArg {
                                name: None,
                                expr: iter_expr,
                            }],
                        }),
                    }
                }

                None => match expected_ty {
                    Some(expected_ty) => {
                        let expected_ty = expected_ty.normalize(tc_state.tys.tys.cons());
                        match expected_ty.con(tc_state.tys.tys.cons()) {
                            Some((con, _)) => {
                                let field_select_expr = ast::L {
                                    loc: loc.clone(),
                                    node: ast::Expr::AssocFnSelect(ast::AssocFnSelectExpr {
                                        ty: con,
                                        ty_user_ty_args: vec![],
                                        member: SmolStr::new_static("fromIter"),
                                        user_ty_args: vec![],
                                        ty_args: vec![],
                                    }),
                                };

                                ast::L {
                                    loc: loc.clone(),
                                    node: ast::Expr::Call(ast::CallExpr {
                                        fun: Box::new(field_select_expr),
                                        args: vec![ast::CallArg {
                                            name: None,
                                            expr: iter_expr,
                                        }],
                                    }),
                                }
                            }
                            None => iter_expr,
                        }
                    }
                    None => iter_expr,
                },
            };

            *expr = desugared;

            check_expr(tc_state, expr, expected_ty, level, loop_stack)
        }
    }
}

pub(super) fn check_match_expr(
    tc_state: &mut TcFunState,
    expr: &mut ast::MatchExpr,
    loc: &ast::Loc,
    expected_ty: Option<&Ty>,
    level: u32,
    loop_stack: &mut Vec<Option<Id>>,
) -> Vec<Ty> {
    use crate::type_checker::pat_coverage::*;

    let ast::MatchExpr { scrutinee, alts } = expr;

    let (scrut_ty, _) = check_expr(tc_state, scrutinee, None, level, loop_stack);

    let mut rhs_tys: Vec<Ty> = Vec::with_capacity(alts.len());

    let mut alt_envs: Vec<Map<Id, Ty>> = Vec::with_capacity(alts.len());

    // Type check patterns first so that the coverage checker can assume patterns are well-typed.
    for ast::Alt {
        pattern,
        guard: _, // checked below to use refined binders in guards
        rhs: _,
    } in alts.iter_mut()
    {
        tc_state.env.enter();

        let pat_ty = check_pat(tc_state, pattern, level);
        unify(
            &pat_ty,
            &scrut_ty,
            tc_state.tys.tys.cons(),
            tc_state.var_gen,
            level,
            &pattern.loc,
        );

        alt_envs.push(tc_state.env.exit());
    }

    let (exhaustive, info) = check_coverage(alts, &scrut_ty, tc_state, loc);

    for (arm_idx, arm) in alts.iter().enumerate() {
        if !info.is_useful(arm_idx as u32) {
            eprintln!("{}: Redundant branch", loc_display(&arm.pattern.loc));
        }
    }

    if !exhaustive {
        eprintln!("{}: Unexhaustive pattern match", loc_display(loc));
    }

    for (
        alt_idx,
        (
            ast::Alt {
                pattern,
                guard,
                rhs,
            },
            mut alt_scope,
        ),
    ) in alts.iter_mut().zip(alt_envs.into_iter()).enumerate()
    {
        refine_binders(&mut alt_scope, &info.bound_vars[alt_idx], &pattern.loc);

        tc_state.env.push_scope(alt_scope);

        // Guards are checked here to use refined binders in the guards.
        if let Some(guard) = guard {
            let (_, guard_binders) =
                check_expr(tc_state, guard, Some(&Ty::bool()), level, loop_stack);
            guard_binders.into_iter().for_each(|(k, v)| {
                tc_state.env.insert(k, v);
            });
        }

        rhs_tys.push(check_stmts(tc_state, rhs, expected_ty, level, loop_stack));

        tc_state.env.exit();
    }

    rhs_tys
}

pub(super) fn check_if_expr(
    tc_state: &mut TcFunState,
    expr: &mut ast::IfExpr,
    expected_ty: Option<&Ty>,
    level: u32,
    loop_stack: &mut Vec<Option<Id>>,
) -> Vec<Ty> {
    let ast::IfExpr {
        branches,
        else_branch,
    } = expr;

    let mut branch_tys: Vec<Ty> = Vec::with_capacity(branches.len() + 1);

    for (cond, body) in branches {
        let (cond_ty, cond_binders) =
            check_expr(tc_state, cond, Some(&Ty::bool()), level, loop_stack);
        unify(
            &cond_ty,
            &Ty::bool(),
            tc_state.tys.tys.cons(),
            tc_state.var_gen,
            level,
            &cond.loc,
        );
        tc_state.env.enter();
        cond_binders.into_iter().for_each(|(k, v)| {
            tc_state.env.insert(k, v);
        });
        let body_ty = check_stmts(tc_state, body, expected_ty, level, loop_stack);
        tc_state.env.exit();
        branch_tys.push(body_ty);
    }

    match else_branch {
        Some(else_body) => {
            let body_ty = check_stmts(tc_state, else_body, expected_ty, level, loop_stack);
            branch_tys.push(body_ty);
        }
        None => {
            // A bit hacky: ensure that without an else branch the expression returns unit.
            branch_tys.push(Ty::unit());
        }
    }

    branch_tys
}

/// Check a `FieldSelect` expr.
///
/// Returns the type of the expression, with updated AST node for the expression.
fn check_field_select(
    tc_state: &mut TcFunState,
    object: &ast::L<ast::Expr>,
    field: &Id,
    user_ty_args: &[ast::L<ast::Type>],
    object_ty: &Ty,
    loc: &ast::Loc,
    level: u32,
) -> (Ty, ast::Expr) {
    // TODO: What if we have a method and a field with the same name?
    match object_ty {
        Ty::Con(con, _) => {
            if let Some(field_ty) = select_field(tc_state, con, &[], field, loc) {
                if !user_ty_args.is_empty() {
                    panic!("{}: Field passed type arguments", loc_display(loc));
                }
                return (
                    field_ty,
                    ast::Expr::FieldSelect(ast::FieldSelectExpr {
                        object: Box::new(object.clone()),
                        field: field.clone(),
                        user_ty_args: vec![],
                    }),
                );
            }
        }

        Ty::App(con, args, _) => {
            if let Some(field_ty) = select_field(tc_state, con, args, field, loc) {
                if !user_ty_args.is_empty() {
                    panic!("{}: Field passed type arguments", loc_display(loc));
                }
                return (
                    field_ty,
                    ast::Expr::FieldSelect(ast::FieldSelectExpr {
                        object: Box::new(object.clone()),
                        field: field.clone(),
                        user_ty_args: vec![],
                    }),
                );
            }
        }

        _ => {}
    }

    let (method_ty_id, scheme) = select_method(tc_state, object_ty, field, loc, level)
        .unwrap_or_else(|| {
            panic!(
                "{}: Type {} does not have field or method {}",
                loc_display(loc),
                object_ty,
                field
            )
        });

    let (method_ty, method_ty_args) = if user_ty_args.is_empty() {
        let (ty, args) = scheme.instantiate(level, tc_state.var_gen, tc_state.preds, loc);
        (ty, args.into_iter().map(Ty::Var).collect())
    } else {
        if scheme.quantified_vars.len() != user_ty_args.len() {
            panic!(
                "{}: Method takes {} type arguments, but applied to {}",
                loc_display(loc),
                scheme.quantified_vars.len(),
                user_ty_args.len()
            );
        }

        let user_ty_args_converted: Vec<Ty> = user_ty_args
            .iter()
            .map(|ty| convert_ast_ty(&tc_state.tys.tys, &ty.node, &ty.loc))
            .collect();

        let ty = scheme.instantiate_with_tys(&user_ty_args_converted, tc_state.preds, loc);

        (ty, user_ty_args_converted)
    };

    // Type arguments of the receiver already substituted for type parameters in
    // `select_method`. Drop 'self' argument.
    match method_ty {
        Ty::Fun {
            mut args,
            ret,
            exceptions,
        } => {
            match &mut args {
                FunArgs::Positional(args) => {
                    let self_arg = args.remove(0);
                    unify(
                        &self_arg,
                        object_ty,
                        tc_state.tys.tys.cons(),
                        tc_state.var_gen,
                        level,
                        loc,
                    );
                }
                FunArgs::Named(_) => panic!(),
            }
            (
                Ty::Fun {
                    args,
                    ret,
                    exceptions,
                },
                ast::Expr::MethodSelect(ast::MethodSelectExpr {
                    object: Box::new(object.clone()),
                    object_ty: Some(object_ty.clone()),
                    method_ty_id,
                    method: field.clone(),
                    ty_args: method_ty_args,
                }),
            )
        }
        _ => panic!(
            "{}: Type of method is not a function type: {:?}",
            loc_display(loc),
            method_ty
        ),
    }
}

/// Try to select a field.
pub(super) fn select_field(
    tc_state: &mut TcFunState,
    ty_con: &Id,
    ty_args: &[Ty],
    field: &Id,
    loc: &ast::Loc,
) -> Option<Ty> {
    let ty_con = tc_state
        .tys
        .tys
        .get_con(ty_con)
        .unwrap_or_else(|| panic!("{}: Unknown type {}", loc_display(loc), ty_con));

    assert_eq!(ty_con.ty_params.len(), ty_args.len());

    match &ty_con.details {
        TyConDetails::Type(TypeDetails { cons, sum }) if !sum => {
            let con_name = cons[0].name.as_ref().unwrap_or(&ty_con.id);
            let con_scheme = tc_state.tys.top_schemes.get(con_name)?;
            let con_ty = con_scheme.instantiate_with_tys(ty_args, tc_state.preds, loc);

            match con_ty {
                Ty::Fun {
                    args: FunArgs::Named(fields),
                    ret: _,
                    exceptions: _,
                } => fields.get(field).cloned(),
                _ => None,
            }
        }

        TyConDetails::Synonym(_) => {
            panic!("{}: Type synonym in select_field", loc_display(loc));
        }

        _ => None,
    }
}

/// Try to select a method (direct or trait). Does not select associated functions.
fn select_method(
    tc_state: &mut TcFunState,
    receiver: &Ty,
    method: &Id,
    loc: &ast::Loc,
    level: u32,
) -> Option<(Id, Scheme)> {
    let mut candidates: Vec<(Id, Scheme)> = vec![];

    for (ty_id, candidate) in tc_state.tys.method_schemes.get(method)? {
        // Don't add predicates to the current predicate set. We will instantiate the scheme again
        // in the call site and use predicates generated from that.
        let (ty, _) = candidate.instantiate(level, tc_state.var_gen, &mut Default::default(), loc);
        let candidate_self_ty = match &ty {
            Ty::Fun {
                args: FunArgs::Positional(args),
                ret: _,
                exceptions: _,
            } => &args[0],

            other => panic!(
                "{}: Method call candidate for {} does not have function type: {}",
                loc_display(loc),
                method,
                other
            ),
        };
        if try_unify_one_way(
            candidate_self_ty,
            receiver,
            tc_state.tys.tys.cons(),
            tc_state.var_gen,
            level,
            loc,
        ) {
            candidates.push((ty_id.clone(), candidate.clone()));
        }
    }

    if candidates.len() > 1 {
        // If there's an associated function among the candidates, pick it. Otherwise fail with an
        // ambiguity error.
        for (i, candidate) in candidates.iter().enumerate() {
            if !tc_state
                .tys
                .tys
                .cons()
                .get(&candidate.0)
                .unwrap()
                .is_trait()
            {
                return Some(candidates.remove(i));
            }
        }

        let candidates_str: Vec<String> = candidates
            .iter()
            .map(|(ty_id, _)| format!("{ty_id}.{method}"))
            .collect();

        panic!(
            "{}: Ambiguous method call, candidates: {}",
            loc_display(loc),
            candidates_str.join(", ")
        );
    }

    candidates.pop()
}

// ty -> [labelOf(ty): ty, ..r] (r is fresh)
//
// Somewhat hackily, we also convert function types that return named types to function types that
// return variants instead, to allow type checking `~Foo(args)` by first converting `Foo`'s type a
// function type that returns a variant, and then applying.
pub(crate) fn make_variant(tc_state: &mut TcFunState, ty: Ty, level: u32, loc: &ast::Loc) -> Ty {
    let con = match ty.normalize(tc_state.tys.tys.cons()) {
        Ty::Con(con, _) | Ty::App(con, _, _) => con,

        Ty::Fun {
            args,
            ret,
            exceptions,
        } => {
            let ret = make_variant(tc_state, *ret, level, loc);
            return Ty::Fun {
                args,
                ret: Box::new(ret),
                exceptions,
            };
        }

        ty => panic!("Type in variant is not a constructor: {ty}"),
    };

    let row_ext = tc_state
        .var_gen
        .new_var(level, Kind::Row(RecordOrVariant::Variant), loc.clone());

    Ty::Anonymous {
        labels: [(con, ty)].into_iter().collect(),
        extension: Some(Box::new(Ty::Var(row_ext))),
        kind: RecordOrVariant::Variant,
        is_row: false,
    }
}

fn refine_binders(scope: &mut Map<Id, Ty>, binders: &Map<Id, Set<Ty>>, loc: &ast::Loc) {
    if cfg!(debug_assertions) {
        let scope_vars: Set<&Id> = scope.keys().collect();
        let binders_vars: Set<&Id> = binders.keys().collect();
        assert_eq!(scope_vars, binders_vars);
    }

    for (var, tys) in binders.iter() {
        // println!("{} --> {:?}", var, tys);
        // assert!(&tys.is_empty());

        if tys.len() == 1 {
            // println!("{} --> {}", var, tys.iter().next().unwrap().clone());
            scope.insert(var.clone(), tys.iter().next().unwrap().clone());
        } else {
            let mut labels: TreeMap<Id, Ty> = Default::default();
            let mut extension: Option<Box<Ty>> = None;

            for ty in tys.iter() {
                match ty {
                    Ty::Con(con, _) | Ty::App(con, _, _) => {
                        let old = labels.insert(con.clone(), ty.clone());
                        assert_eq!(old, None);
                    }

                    Ty::Var(_) | Ty::QVar(_, _) => {
                        // Get the row type from the non-refined binding.
                        extension = Some(Box::new(ty.clone()));
                    }

                    Ty::Anonymous {
                        labels,
                        extension: new_extension,
                        kind: RecordOrVariant::Variant,
                        is_row,
                    } => {
                        // This part is quite hacky and possibly wrong: because we only refine
                        // variants, and we can't ahve nested variants, and we check one type at a
                        // time when checking variant coverage, this case can only mean `[..r]` (for
                        // some `r`), and matching it means the value being matched can have the
                        // extension.
                        assert!(!is_row);
                        assert!(labels.is_empty());
                        extension = new_extension.clone();
                    }

                    Ty::Fun { .. } | Ty::Anonymous { .. } => panic!("{}: {}", loc_display(loc), ty),
                }
            }

            let new_ty = Ty::Anonymous {
                labels,
                extension,
                kind: RecordOrVariant::Variant,
                is_row: false,
            };

            // println!("{} --> {}", var, new_ty);

            scope.insert(var.clone(), new_ty);
        }
    }
}
