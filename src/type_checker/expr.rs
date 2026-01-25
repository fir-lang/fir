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
    expr: &mut ast::Expr,
    loc: &ast::Loc,
    expected_ty: Option<&Ty>,
    level: u32,
    loop_stack: &mut Vec<Option<Id>>,
) -> (Ty, HashMap<Id, Ty>) {
    match expr {
        ast::Expr::Var(ast::VarExpr {
            id: var,
            user_ty_args,
            ty_args,
            inferred_ty,
        }) => {
            assert!(inferred_ty.is_none());
            assert!(ty_args.is_empty());

            // Check if local.
            if let Some(ty) = tc_state.env.get(var) {
                if !user_ty_args.is_empty() {
                    panic!(
                        "{}: Local variables can't have type parameters, but `{}` is passed type arguments",
                        loc_display(loc),
                        var
                    );
                }
                *inferred_ty = Some(ty.clone());
                return (
                    unify_expected_ty(
                        ty.clone(),
                        expected_ty,
                        tc_state.tys.tys.cons(),
                        tc_state.var_gen,
                        level,
                        loc,
                    ),
                    Default::default(),
                );
            }

            let scheme = match tc_state.tys.top_schemes.get(var) {
                Some(scheme) => scheme,
                None => panic!("{}: Unbound variable {}", loc_display(loc), var),
            };

            let ty = if user_ty_args.is_empty() {
                let (ty, ty_args) =
                    scheme.instantiate(level, tc_state.var_gen, tc_state.preds, loc);

                *expr = ast::Expr::Var(ast::VarExpr {
                    id: var.clone(),
                    user_ty_args: vec![],
                    ty_args: ty_args.into_iter().map(Ty::UVar).collect(),
                    inferred_ty: Some(ty.clone()),
                });

                ty
            } else {
                if scheme.quantified_vars.len() != user_ty_args.len() {
                    panic!(
                        "{}: Variable {} takes {} type arguments, but applied to {}",
                        loc_display(loc),
                        var,
                        scheme.quantified_vars.len(),
                        user_ty_args.len()
                    );
                }

                let user_ty_args_converted: Vec<Ty> = user_ty_args
                    .iter()
                    .map(|ty| convert_ast_ty(&tc_state.tys.tys, &ty.node, &ty.loc))
                    .collect();

                let ty = scheme.instantiate_with_tys(&user_ty_args_converted, tc_state.preds, loc);

                *expr = ast::Expr::Var(ast::VarExpr {
                    id: var.clone(),
                    user_ty_args: vec![],
                    ty_args: user_ty_args_converted,
                    inferred_ty: Some(ty.clone()),
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
                    loc,
                ),
                Default::default(),
            )
        }

        // <object:Expr>.<field:Id>.
        // This updates the expression as `MethodSelect` if the `field` turns out to be a method.
        ast::Expr::FieldSel(ast::FieldSelExpr {
            object,
            field,
            user_ty_args,
            inferred_ty,
        }) => {
            assert!(inferred_ty.is_none());

            let ty = {
                let (object_ty, _) = check_expr(
                    tc_state,
                    &mut object.node,
                    &object.loc,
                    None,
                    level,
                    loop_stack,
                );

                let ty_normalized = object_ty.normalize(tc_state.tys.tys.cons());
                match &ty_normalized {
                    Ty::Anonymous {
                        labels,
                        extension,
                        kind: RecordOrVariant::Record,
                        ..
                    } => {
                        if !user_ty_args.is_empty() {
                            panic!("{}: Record field with type arguments", loc_display(loc));
                        }
                        let (labels, _) = crate::type_checker::row_utils::collect_rows(
                            tc_state.tys.tys.cons(),
                            &ty_normalized,
                            RecordOrVariant::Record,
                            labels,
                            extension.clone(),
                        );
                        let ty = match labels.get(field) {
                            Some(field_ty) => field_ty.clone(),
                            None => panic!(
                                "{}: Record with fields {:?} does not have field {}",
                                loc_display(&object.loc),
                                labels.keys().collect::<Vec<_>>(),
                                field
                            ),
                        };
                        *inferred_ty = Some(ty.clone());
                        ty
                    }

                    other => {
                        let (ty, new_expr) = check_field_sel(
                            tc_state,
                            object,
                            field,
                            user_ty_args,
                            other,
                            loc,
                            level,
                        );
                        *expr = new_expr;
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
                    loc,
                ),
                Default::default(),
            )
        }

        ast::Expr::MethodSel(_) => panic!("MethodSel in type checker"),

        ast::Expr::ConSel(ast::Con {
            ty,
            con,
            user_ty_args,
            ty_args,
        }) => {
            assert!(ty_args.is_empty());

            let ty_con: &TyCon = tc_state
                .tys
                .tys
                .cons()
                .get(ty)
                .unwrap_or_else(|| panic!("{}: Unknown type {}", loc_display(loc), ty));

            let ty_details: &TypeDetails = ty_con.type_details().unwrap_or_else(|| {
                panic!(
                    "{}: Type {} is a trait or type synonym",
                    loc_display(loc),
                    ty
                )
            });

            let scheme: &Scheme = match con {
                Some(con) => {
                    if !ty_details.sum {
                        panic!(
                            "{}: Type {} does not have sum constructors",
                            loc_display(loc),
                            ty
                        );
                    }
                    ty_details.cons.get(con).unwrap_or_else(|| {
                        panic!(
                            "{}: Type {} does not have a constructor named {}",
                            loc_display(loc),
                            ty,
                            con
                        )
                    })
                }

                None => {
                    if ty_details.sum {
                        panic!(
                            "{}: Sum type allocation {} needs a constructor",
                            loc_display(loc),
                            ty
                        );
                    }
                    assert_eq!(ty_details.cons.len(), 1);
                    ty_details.cons.values().next().unwrap()
                }
            };

            let con_ty = if user_ty_args.is_empty() {
                let (con_ty, con_ty_args) =
                    scheme.instantiate(level, tc_state.var_gen, tc_state.preds, loc);

                *expr = ast::Expr::ConSel(ast::Con {
                    ty: ty.clone(),
                    con: con.clone(),
                    user_ty_args: vec![],
                    ty_args: con_ty_args.into_iter().map(Ty::UVar).collect(),
                });

                con_ty
            } else {
                if scheme.quantified_vars.len() != user_ty_args.len() {
                    panic!(
                        "{}: Constructor {}{}{} takes {} type arguments, but applied to {}",
                        loc_display(loc),
                        ty,
                        if con.is_some() { "." } else { "" },
                        con.as_ref().cloned().unwrap_or(SmolStr::new_static("")),
                        scheme.quantified_vars.len(),
                        user_ty_args.len()
                    );
                }

                let user_ty_args_converted: Vec<Ty> = user_ty_args
                    .iter()
                    .map(|ty| convert_ast_ty(&tc_state.tys.tys, &ty.node, &ty.loc))
                    .collect();

                let con_ty =
                    scheme.instantiate_with_tys(&user_ty_args_converted, tc_state.preds, loc);

                *expr = ast::Expr::ConSel(ast::Con {
                    ty: ty.clone(),
                    con: con.clone(),
                    user_ty_args: vec![],
                    ty_args: user_ty_args_converted,
                });

                con_ty
            };

            (
                unify_expected_ty(
                    con_ty,
                    expected_ty,
                    tc_state.tys.tys.cons(),
                    tc_state.var_gen,
                    level,
                    loc,
                ),
                Default::default(),
            )
        }

        ast::Expr::AssocFnSel(ast::AssocFnSelExpr {
            ty,
            ty_user_ty_args,
            member,
            user_ty_args,
            ty_args,
            inferred_ty,
        }) => {
            assert!(inferred_ty.is_none());
            assert!(ty_args.is_empty());

            if !ty_user_ty_args.is_empty() {
                let con = tc_state
                    .tys
                    .tys
                    .get_con(ty)
                    .unwrap_or_else(|| panic!("{}: Unknown type {}", loc_display(loc), ty));

                if con.ty_params.len() != ty_user_ty_args.len() {
                    panic!(
                        "{}: Type {} takes {} type arguments, but applied to {}",
                        loc_display(loc),
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
                .unwrap_or_else(|| panic!("{}: Unknown type {}", loc_display(loc), ty))
                .get(member)
                .unwrap_or_else(|| {
                    panic!(
                        "{}: Type {} does not have associated function {}",
                        loc_display(loc),
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
                    loc,
                );
            }

            let method_ty = if user_ty_args_converted.is_empty() {
                let (method_ty, method_ty_args) =
                    scheme.instantiate(level, tc_state.var_gen, tc_state.preds, loc);

                for (ty_ty_arg, method_ty_arg) in
                    ty_user_ty_args_converted.iter().zip(method_ty_args.iter())
                {
                    unify(
                        ty_ty_arg,
                        &Ty::UVar(method_ty_arg.clone()),
                        tc_state.tys.tys.cons(),
                        tc_state.var_gen,
                        level,
                        loc,
                    );
                }

                *expr = ast::Expr::AssocFnSel(ast::AssocFnSelExpr {
                    ty: ty.clone(),
                    ty_user_ty_args: vec![],
                    member: member.clone(),
                    user_ty_args: vec![],
                    ty_args: method_ty_args.into_iter().map(Ty::UVar).collect(),
                    inferred_ty: Some(method_ty.clone()),
                });

                method_ty
            } else {
                if scheme.quantified_vars.len() != user_ty_args.len() {
                    panic!(
                        "{}: Associated function {}.{} takes {} type arguments, but applied to {}",
                        loc_display(loc),
                        ty,
                        member,
                        scheme.quantified_vars.len(),
                        user_ty_args.len()
                    );
                }

                let method_ty =
                    scheme.instantiate_with_tys(&user_ty_args_converted, tc_state.preds, loc);

                *expr = ast::Expr::AssocFnSel(ast::AssocFnSelExpr {
                    ty: ty.clone(),
                    ty_user_ty_args: vec![],
                    member: member.clone(),
                    user_ty_args: vec![],
                    ty_args: user_ty_args_converted,
                    inferred_ty: Some(method_ty.clone()),
                });

                method_ty
            };

            let expr_ty = unify_expected_ty(
                method_ty,
                expected_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                loc,
            );

            (expr_ty, Default::default())
        }

        ast::Expr::Call(ast::CallExpr {
            fun,
            args,
            inferred_ty,
        }) => {
            assert!(inferred_ty.is_none());

            let (fun_ty, _) =
                check_expr(tc_state, &mut fun.node, &fun.loc, None, level, loop_stack);

            let fun_ty = fun_ty.normalize(tc_state.tys.tys.cons());

            let ret_ty = match &fun_ty {
                Ty::Fun {
                    args: param_tys,
                    ret: ret_ty,
                    exceptions,
                } => {
                    if param_tys.len() != args.len() {
                        panic!(
                            "{}: Function with arity {} is passed {} args",
                            loc_display(loc),
                            param_tys.len(),
                            args.len()
                        );
                    }

                    let ret_ty = unify_expected_ty(
                        (**ret_ty).clone(),
                        expected_ty,
                        tc_state.tys.tys.cons(),
                        tc_state.var_gen,
                        level,
                        loc,
                    );

                    match param_tys {
                        FunArgs::Positional(param_tys) => {
                            for arg in args.iter() {
                                if arg.name.is_some() {
                                    panic!(
                                        "{}: Named argument applied to function that expects positional arguments",
                                        loc_display(loc),
                                    );
                                }
                            }

                            let mut arg_tys: Vec<Ty> = Vec::with_capacity(args.len());
                            for (param_ty, arg) in param_tys.iter().zip(args.iter_mut()) {
                                let (arg_ty, _) = check_expr(
                                    tc_state,
                                    &mut arg.expr.node,
                                    &arg.expr.loc,
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
                                            inferred_ty: _,
                                        }) => {
                                            arg.name = Some(id.clone());
                                        }
                                        _ => {
                                            panic!(
                                                "{}: Positional argument applied to function that expects named arguments",
                                                loc_display(loc),
                                            );
                                        }
                                    }
                                }
                            }

                            let param_names: HashSet<&Id> = param_tys.keys().collect();
                            let arg_names: HashSet<&Id> =
                                args.iter().map(|arg| arg.name.as_ref().unwrap()).collect();

                            if param_names != arg_names {
                                panic!(
                                    "{}: Function expects arguments with names {:?}, but passed {:?}",
                                    loc_display(loc),
                                    param_names,
                                    arg_names
                                );
                            }

                            for arg in args.iter_mut() {
                                let arg_name: &Id = arg.name.as_ref().unwrap();
                                let param_ty: &Ty = param_tys.get(arg_name).unwrap();
                                let (arg_ty, _) = check_expr(
                                    tc_state,
                                    &mut arg.expr.node,
                                    &arg.expr.loc,
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
                                    loc,
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
                            loc,
                        );
                    }

                    ret_ty
                }

                _ => panic!(
                    "{}: Function in function application is not a function: {:?}",
                    loc_display(loc),
                    fun_ty,
                ),
            };

            // If the callee is a method and called directly, convert it into an associated function
            // call to avoid closure allocation.
            if let ast::Expr::MethodSel(ast::MethodSelExpr {
                object,
                object_ty: _,
                method_ty_id,
                method,
                ty_args,
                inferred_ty,
            }) = &fun.node
            {
                assert_eq!(inferred_ty.as_ref().unwrap(), &fun_ty);

                // Methods can't have named arguments.
                args.insert(
                    0,
                    ast::CallArg {
                        name: None,
                        expr: (**object).clone(),
                    },
                );

                fun.node = ast::Expr::AssocFnSel(ast::AssocFnSelExpr {
                    ty: method_ty_id.clone(),
                    ty_user_ty_args: vec![], // unused after type checking
                    member: method.clone(),
                    user_ty_args: vec![], // unused after type checking
                    ty_args: ty_args.clone(),
                    inferred_ty: Some(fun_ty.clone()),
                });
            }

            *inferred_ty = Some(ret_ty.clone());

            (ret_ty, Default::default())
        }

        ast::Expr::Int(ast::IntExpr { text, kind, parsed }) => {
            assert!(kind.is_none());

            // This should be an `IntExpr` method to avoid having to know about the lexical syntax
            // of integers in the type checker, but we run into issues when we try to borrow `kind`
            // mutably above while also having a ref to `IntExpr`.
            let negate = text.starts_with('-');

            let expected_ty = expected_ty.map(|ty| ty.normalize(tc_state.tys.tys.cons()));

            let con = match &expected_ty {
                Some(Ty::Con(con, _kind)) => con.as_str(),

                Some(Ty::UVar(var)) => {
                    // Default as I32.
                    // Note: the error order when there's a unification error + integer literal
                    // error (i.e. integer too large/small) here vs. in the rest of the cases.
                    unify(
                        &Ty::UVar(var.clone()),
                        &Ty::Con(SmolStr::new_static("I32"), Kind::Star),
                        tc_state.tys.tys.cons(),
                        tc_state.var_gen,
                        level,
                        loc,
                    );
                    "I32"
                }

                Some(other) => {
                    panic!(
                        "{}: Expected {}, found integer literal",
                        loc_display(loc),
                        other,
                    )
                }

                None => {
                    // Default as I32.
                    "I32"
                }
            };

            match con {
                "U8" => {
                    if negate {
                        panic!(
                            "{}: Cannot negate unsigned integer: {}",
                            loc_display(loc),
                            text
                        );
                    }
                    *kind = Some(ast::IntKind::U8(u8::try_from(*parsed).unwrap_or_else(
                        |_| {
                            panic!(
                                "{}: Integer literal {} out of range for U8",
                                loc_display(loc),
                                text
                            )
                        },
                    )));
                }

                "I8" => {
                    let mut bits = u8::try_from(*parsed).unwrap_or_else(|_| {
                        panic!(
                            "{}: Integer literal {} out of range for I8",
                            loc_display(loc),
                            text
                        )
                    });
                    let limit = if negate { i8::MIN } else { i8::MAX }.unsigned_abs();
                    if bits > limit {
                        panic!(
                            "{}: Integer literal {} out of range for I8",
                            loc_display(loc),
                            text
                        );
                    }
                    if negate {
                        bits = !bits.wrapping_sub(1);
                    }
                    *kind = Some(ast::IntKind::I8(bits as i8));
                }

                "U32" => {
                    if negate {
                        panic!(
                            "{}: Cannot negate unsigned integer: {}",
                            loc_display(loc),
                            text
                        );
                    }
                    *kind = Some(ast::IntKind::U32(u32::try_from(*parsed).unwrap_or_else(
                        |_| {
                            panic!(
                                "{}: Integer literal {} out of range for U32",
                                loc_display(loc),
                                text
                            )
                        },
                    )));
                }

                "I32" => {
                    let mut bits = u32::try_from(*parsed).unwrap_or_else(|_| {
                        panic!(
                            "{}: Integer literal {} out of range for I32",
                            loc_display(loc),
                            text
                        )
                    });
                    let limit = if negate { i32::MIN } else { i32::MAX }.unsigned_abs();
                    if bits > limit {
                        panic!(
                            "{}: Integer literal {} out of range for I32",
                            loc_display(loc),
                            text
                        );
                    }
                    if negate {
                        bits = !bits.wrapping_sub(1);
                    }
                    *kind = Some(ast::IntKind::I32(bits as i32));
                }

                "U64" => {
                    if negate {
                        panic!(
                            "{}: Cannot negate unsigned integer: {}",
                            loc_display(loc),
                            text
                        );
                    }
                    *kind = Some(ast::IntKind::U64(*parsed));
                }

                "I64" => {
                    let mut bits = *parsed;
                    let limit = if negate { i64::MIN } else { i64::MAX }.unsigned_abs();
                    if bits > limit {
                        panic!(
                            "{}: Integer literal {} out of range for I32",
                            loc_display(loc),
                            text
                        );
                    }
                    if negate {
                        bits = !bits.wrapping_sub(1);
                    }
                    *kind = Some(ast::IntKind::I64(bits as i64));
                }

                other => panic!(
                    "{}: Expected {}, found integer literal",
                    loc_display(loc),
                    other,
                ),
            }

            (Ty::Con(SmolStr::new(con), Kind::Star), Default::default())
        }

        ast::Expr::Str(og_parts) => {
            let ty = unify_expected_ty(
                Ty::str(),
                expected_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                loc,
            );

            let ret = (ty, Default::default());

            if og_parts.len() == 1
                && let StrPart::Str(_) = &og_parts[0]
            {
                return ret;
            }

            /*
            "part1 `part2` ..."

            ==>

            do:
                let buf = StrBuf.withCapacity(0)
                buf.pushStr(part1)
                buf.pushStr(part2.toStr())
                ...
                buf.toStr()
            */

            let parts = std::mem::take(og_parts);

            let buf_id = SmolStr::new_static("$buf$");

            let str_buf_ty = Ty::Con(SmolStr::new_static("StrBuf"), Kind::Star);

            let mut desugared_stmts: Vec<ast::L<ast::Stmt>> = vec![ast::L {
                loc: loc.clone(),
                node: ast::Stmt::Let(ast::LetStmt {
                    lhs: ast::L {
                        loc: loc.clone(),
                        node: ast::Pat::Var(ast::VarPat {
                            var: buf_id.clone(),
                            ty: Some(str_buf_ty.clone()),
                        }),
                    },
                    ty: None,
                    rhs: ast::L {
                        loc: loc.clone(),
                        node: ast::Expr::Call(ast::CallExpr {
                            fun: Box::new(ast::L {
                                loc: loc.clone(),
                                node: ast::Expr::AssocFnSel(ast::AssocFnSelExpr {
                                    ty: SmolStr::new_static("StrBuf"),
                                    ty_user_ty_args: vec![],
                                    member: SmolStr::new_static("empty"),
                                    user_ty_args: vec![],
                                    ty_args: vec![tc_state.exceptions.clone()],
                                    inferred_ty: Some(Ty::Fun {
                                        args: FunArgs::Positional(vec![]),
                                        ret: Box::new(str_buf_ty.clone()),
                                        exceptions: Some(Box::new(tc_state.exceptions.clone())),
                                    }),
                                }),
                            }),
                            args: vec![],
                            inferred_ty: Some(str_buf_ty.clone()),
                        }),
                    },
                }),
            }];

            let make_push = |arg: ast::L<ast::Expr>, exn: Ty| -> ast::L<ast::Stmt> {
                ast::L {
                    loc: loc.clone(),
                    node: ast::Stmt::Expr(ast::Expr::Call(ast::CallExpr {
                        fun: Box::new(ast::L {
                            loc: loc.clone(),
                            node: ast::Expr::AssocFnSel(ast::AssocFnSelExpr {
                                ty: SmolStr::new_static("StrBuf"),
                                ty_user_ty_args: vec![],
                                member: SmolStr::new_static("pushStr"),
                                user_ty_args: vec![],
                                ty_args: vec![exn.clone()],
                                inferred_ty: Some(Ty::Fun {
                                    args: FunArgs::Positional(vec![
                                        str_buf_ty.clone(),
                                        Ty::Con(SmolStr::new_static("Str"), Kind::Star),
                                    ]),
                                    ret: Box::new(Ty::unit()),
                                    exceptions: Some(Box::new(exn)),
                                }),
                            }),
                        }),
                        args: vec![
                            ast::CallArg {
                                name: None,
                                expr: ast::L {
                                    loc: loc.clone(),
                                    node: ast::Expr::Var(ast::VarExpr {
                                        id: buf_id.clone(),
                                        user_ty_args: vec![],
                                        ty_args: vec![],
                                        inferred_ty: Some(str_buf_ty.clone()),
                                    }),
                                },
                            },
                            ast::CallArg {
                                name: None,
                                expr: arg,
                            },
                        ],
                        inferred_ty: Some(Ty::unit()),
                    })),
                }
            };

            for part in parts {
                match part {
                    StrPart::Str(str) => desugared_stmts.push(make_push(
                        ast::L {
                            loc: loc.clone(),
                            node: ast::Expr::Str(vec![StrPart::Str(str)]),
                        },
                        tc_state.exceptions.clone(),
                    )),
                    StrPart::Expr(mut expr) => {
                        let expr_var =
                            tc_state
                                .var_gen
                                .new_var(level, Kind::Star, expr.loc.clone());
                        tc_state.preds.push(Pred {
                            trait_: Ty::to_str_id(),
                            params: vec![Ty::UVar(expr_var.clone())],
                            loc: expr.loc.clone(),
                        });
                        let (part_ty, _) = check_expr(
                            tc_state,
                            &mut expr.node,
                            &expr.loc,
                            Some(&Ty::UVar(expr_var)),
                            level,
                            loop_stack,
                        );
                        let expr_node = replace(&mut expr.node, ast::Expr::Char('a'));
                        expr.node = ast::Expr::Call(ast::CallExpr {
                            fun: Box::new(ast::L {
                                // ToStr.toStr[t, exn](self: t) Str / exn
                                node: ast::Expr::AssocFnSel(ast::AssocFnSelExpr {
                                    ty: SmolStr::new_static("ToStr"),
                                    ty_user_ty_args: vec![],
                                    member: SmolStr::new_static("toStr"),
                                    user_ty_args: vec![],
                                    ty_args: vec![part_ty.clone(), tc_state.exceptions.clone()],
                                    inferred_ty: Some(Ty::Fun {
                                        args: FunArgs::Positional(vec![part_ty]),
                                        ret: Box::new(Ty::Con(
                                            SmolStr::new_static("Str"),
                                            Kind::Star,
                                        )),
                                        exceptions: Some(Box::new(tc_state.exceptions.clone())),
                                    }),
                                }),
                                loc: expr.loc.clone(),
                            }),
                            args: vec![ast::CallArg {
                                name: None,
                                expr: ast::L {
                                    node: expr_node,
                                    loc: expr.loc.clone(),
                                },
                            }],
                            inferred_ty: Some(Ty::Con(SmolStr::new_static("Con"), Kind::Star)),
                        });
                        desugared_stmts.push(make_push(expr, tc_state.exceptions.clone()));
                    }
                }
            }

            desugared_stmts.push(ast::L {
                loc: loc.clone(),
                node: ast::Stmt::Expr(ast::Expr::Call(ast::CallExpr {
                    fun: Box::new(ast::L {
                        // ToStr.toStr[t, exn](self: t) Str / exn
                        node: ast::Expr::AssocFnSel(ast::AssocFnSelExpr {
                            ty: SmolStr::new_static("ToStr"),
                            ty_user_ty_args: vec![],
                            member: SmolStr::new_static("toStr"),
                            user_ty_args: vec![],
                            ty_args: vec![str_buf_ty.clone(), tc_state.exceptions.clone()],
                            inferred_ty: Some(Ty::Fun {
                                args: FunArgs::Positional(vec![str_buf_ty.clone()]),
                                ret: Box::new(Ty::Con(SmolStr::new_static("Str"), Kind::Star)),
                                exceptions: Some(Box::new(tc_state.exceptions.clone())),
                            }),
                        }),
                        loc: loc.clone(),
                    }),
                    args: vec![ast::CallArg {
                        name: None,
                        expr: ast::L {
                            node: ast::Expr::Var(ast::VarExpr {
                                id: buf_id.clone(),
                                user_ty_args: vec![],
                                ty_args: vec![],
                                inferred_ty: Some(str_buf_ty.clone()),
                            }),
                            loc: loc.clone(),
                        },
                    }],
                    inferred_ty: Some(Ty::Con(SmolStr::new_static("Con"), Kind::Star)),
                })),
            });

            *expr = ast::Expr::Do(ast::DoExpr {
                stmts: desugared_stmts,
                inferred_ty: Some(ret.0.clone()),
            });

            ret
        }

        ast::Expr::Char(_) => (
            unify_expected_ty(
                Ty::char(),
                expected_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                loc,
            ),
            Default::default(),
        ),

        ast::Expr::BinOp(ast::BinOpExpr { left, right, op }) => {
            let method = match op {
                ast::BinOp::And => {
                    let bool_ty = Ty::Con("Bool".into(), Kind::Star);
                    let (_, mut left_binders) = check_expr(
                        tc_state,
                        &mut left.node,
                        &left.loc,
                        Some(&bool_ty),
                        level,
                        loop_stack,
                    );
                    tc_state.env.enter();
                    left_binders.iter().for_each(|(k, v)| {
                        tc_state.env.insert(k.clone(), v.clone());
                    });
                    let (_, right_binders) = check_expr(
                        tc_state,
                        &mut right.node,
                        &right.loc,
                        Some(&bool_ty),
                        level,
                        loop_stack,
                    );
                    tc_state.env.exit();

                    let left_binder_vars: HashSet<&Id> = left_binders.keys().collect();
                    let right_binder_vars: HashSet<&Id> = right_binders.keys().collect();
                    if !left_binder_vars.is_disjoint(&right_binder_vars) {
                        let intersection: Vec<Id> = left_binder_vars
                            .intersection(&right_binder_vars)
                            .map(|id| (**id).clone())
                            .collect();
                        panic!(
                            "{}: Left and right exprs in `and` bind same variables: {}",
                            loc_display(loc),
                            intersection.join(", "),
                        );
                    }

                    left_binders.extend(right_binders);
                    return (bool_ty, left_binders);
                }

                ast::BinOp::Or => {
                    let bool_ty = Ty::Con("Bool".into(), Kind::Star);
                    check_expr(
                        tc_state,
                        &mut left.node,
                        &left.loc,
                        Some(&bool_ty),
                        level,
                        loop_stack,
                    );
                    check_expr(
                        tc_state,
                        &mut right.node,
                        &right.loc,
                        Some(&bool_ty),
                        level,
                        loop_stack,
                    );
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

            *expr = ast::Expr::Call(ast::CallExpr {
                fun: Box::new(ast::L {
                    loc: left.loc.clone(),
                    node: ast::Expr::FieldSel(ast::FieldSelExpr {
                        object: left.clone(),
                        field: SmolStr::new_static(method),
                        user_ty_args: vec![],
                        inferred_ty: None,
                    }),
                }),
                args: vec![ast::CallArg {
                    name: None,
                    expr: (**right).clone(),
                }],
                inferred_ty: None,
            });

            check_expr(tc_state, expr, loc, expected_ty, level, loop_stack)
        }

        ast::Expr::UnOp(ast::UnOpExpr { op, expr: arg }) => match op {
            ast::UnOp::Not => {
                let (ty, _) = check_expr(
                    tc_state,
                    &mut arg.node,
                    &arg.loc,
                    Some(&Ty::bool()),
                    level,
                    loop_stack,
                );
                *expr = ast::Expr::Call(ast::CallExpr {
                    fun: Box::new(ast::L {
                        loc: arg.loc.clone(),
                        node: ast::Expr::AssocFnSel(ast::AssocFnSelExpr {
                            ty: SmolStr::new_static("Bool"),
                            ty_user_ty_args: vec![],
                            member: SmolStr::new_static("__not"),
                            user_ty_args: vec![],
                            ty_args: vec![tc_state.exceptions.clone()],
                            inferred_ty: Some(Ty::Fun {
                                args: FunArgs::Positional(vec![Ty::Con(
                                    SmolStr::new("Bool"),
                                    Kind::Star,
                                )]),
                                ret: Box::new(Ty::Con(SmolStr::new("Bool"), Kind::Star)),
                                exceptions: Some(Box::new(tc_state.exceptions.clone())),
                            }),
                        }),
                    }),
                    args: vec![ast::CallArg {
                        name: None,
                        expr: *arg.clone(),
                    }],
                    inferred_ty: Some(Ty::bool()),
                });
                (ty, Default::default())
            }

            ast::UnOp::Neg => {
                *expr = ast::Expr::Call(ast::CallExpr {
                    fun: Box::new(ast::L {
                        loc: arg.loc.clone(),
                        node: ast::Expr::FieldSel(ast::FieldSelExpr {
                            object: arg.clone(),
                            field: SmolStr::new_static("__neg"),
                            user_ty_args: vec![],
                            inferred_ty: None,
                        }),
                    }),
                    args: vec![],
                    inferred_ty: None,
                });
                check_expr(tc_state, expr, loc, expected_ty, level, loop_stack)
            }
        },

        ast::Expr::Return(ast::ReturnExpr { expr, inferred_ty }) => {
            assert!(inferred_ty.is_none());
            let return_ty = tc_state.return_ty.clone();
            check_expr(
                tc_state,
                &mut expr.node,
                loc,
                Some(&return_ty),
                level,
                loop_stack,
            );
            let expr_ty = expected_ty.cloned().unwrap_or_else(|| {
                Ty::UVar(
                    tc_state
                        .var_gen
                        .new_var(level, Kind::Star, expr.loc.clone()),
                )
            });
            *inferred_ty = Some(expr_ty.clone());
            (expr_ty, Default::default())
        }

        ast::Expr::Match(match_expr) => {
            let mut rhs_tys =
                check_match_expr(tc_state, match_expr, loc, expected_ty, level, loop_stack);

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
                    loc,
                );
            }

            // Same as above, only useful when `expected_ty` is not available.
            let expr_ty = unify_expected_ty(
                rhs_tys.pop().unwrap(),
                expected_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                loc,
            );
            match_expr.inferred_ty = Some(expr_ty.clone());
            (expr_ty, Default::default())
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
                            loc,
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
                            loc,
                        );
                    }
                }
            }

            let expr_ty = branch_tys.pop().unwrap();
            if_expr.inferred_ty = Some(expr_ty.clone());
            (expr_ty, Default::default())
        }

        ast::Expr::Fn(ast::FnExpr {
            sig,
            body,
            inferred_ty,
        }) => {
            assert!(sig.context.type_params.is_empty());
            assert!(sig.context.preds.is_empty());
            assert!(matches!(&sig.self_, ast::SelfParam::No));
            assert!(inferred_ty.is_none());

            let (expected_args, expected_ret, expected_exceptions) = match expected_ty {
                Some(expected_ty) => match expected_ty.normalize(tc_state.tys.tys.cons()) {
                    Ty::Fun {
                        args,
                        ret,
                        exceptions,
                    } => (Some(args), Some(ret), Some(exceptions)),

                    Ty::Con(_, _)
                    | Ty::UVar(_)
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
                    None => Ty::UVar(tc_state.var_gen.new_var(level + 1, Kind::Star, loc.clone())),
                },
            };

            let exceptions = match &sig.exceptions {
                Some(exc) => convert_ast_ty(&tc_state.tys.tys, &exc.node, &exc.loc),
                None => match expected_exceptions {
                    Some(Some(exn)) => (*exn).clone(),
                    _ => Ty::UVar(tc_state.var_gen.new_var(level + 1, Kind::Star, loc.clone())),
                },
            };

            let mut param_tys: Vec<Ty> = Vec::with_capacity(sig.params.len());
            for (param_idx, (param_name, param_ty)) in sig.params.iter().enumerate() {
                let param_ty_converted: Option<Ty> = param_ty
                    .as_ref()
                    .map(|param_ty| convert_ast_ty(&tc_state.tys.tys, &param_ty.node, loc));

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
                                loc_display(loc)
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
                loc,
            );
            *inferred_ty = Some(ty.clone());
            (ty, Default::default())
        }

        ast::Expr::Is(ast::IsExpr { expr, pat }) => {
            let (expr_ty, _) =
                check_expr(tc_state, &mut expr.node, &expr.loc, None, level, loop_stack);
            tc_state.env.enter();
            let pat_ty = check_pat(tc_state, pat, level);
            let pat_binders: HashMap<Id, Ty> = tc_state.env.exit();
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

        ast::Expr::Do(ast::DoExpr { stmts, inferred_ty }) => {
            assert!(inferred_ty.is_none());
            tc_state.env.enter();
            let ty = check_stmts(tc_state, stmts, expected_ty, level, loop_stack);
            tc_state.env.exit();
            *inferred_ty = Some(ty.clone());
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
                                inferred_ty: None,
                            }),
                        }),
                        args: vec![],
                        inferred_ty: None,
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
                        loc_display(loc)
                    );
                }

                let mut elem_iters: Vec<ast::L<ast::Expr>> = Vec::with_capacity(elems.len());
                for (k, v) in elems.iter() {
                    let elem = match k {
                        Some(k) => ast::L {
                            loc: loc.clone(),
                            node: ast::Expr::Record(ast::RecordExpr {
                                fields: vec![
                                    (SmolStr::new("key"), k.clone()),
                                    (SmolStr::new("val"), v.clone()),
                                ],
                                inferred_ty: None,
                            }),
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
                                    inferred_ty: None,
                                }),
                            }),
                            args: vec![ast::CallArg {
                                name: None,
                                expr: elem,
                            }],
                            inferred_ty: None,
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
                            node: ast::Expr::FieldSel(ast::FieldSelExpr {
                                object: Box::new(elem),
                                field: SmolStr::new_static("chain"),
                                user_ty_args: vec![],
                                inferred_ty: None,
                            }),
                        }),
                        args: vec![ast::CallArg {
                            name: None,
                            expr: next,
                        }],
                        inferred_ty: None,
                    }),
                })
            };

            let desugared = match iter_ty {
                Some(iter_ty) => {
                    let field_sel_expr = ast::L {
                        loc: loc.clone(),
                        node: ast::Expr::AssocFnSel(ast::AssocFnSelExpr {
                            ty: iter_ty,
                            ty_user_ty_args: vec![],
                            member: SmolStr::new_static("fromIter"),
                            user_ty_args: vec![],
                            ty_args: vec![],
                            inferred_ty: None,
                        }),
                    };

                    ast::Expr::Call(ast::CallExpr {
                        fun: Box::new(field_sel_expr),
                        args: vec![ast::CallArg {
                            name: None,
                            expr: iter_expr,
                        }],
                        inferred_ty: None,
                    })
                }

                None => match expected_ty {
                    Some(expected_ty) => {
                        let expected_ty = expected_ty.normalize(tc_state.tys.tys.cons());
                        match expected_ty.con(tc_state.tys.tys.cons()) {
                            Some((con, _)) => {
                                let field_select_expr = ast::L {
                                    loc: loc.clone(),
                                    node: ast::Expr::AssocFnSel(ast::AssocFnSelExpr {
                                        ty: con,
                                        ty_user_ty_args: vec![],
                                        member: SmolStr::new_static("fromIter"),
                                        user_ty_args: vec![],
                                        ty_args: vec![],
                                        inferred_ty: None,
                                    }),
                                };

                                ast::Expr::Call(ast::CallExpr {
                                    fun: Box::new(field_select_expr),
                                    args: vec![ast::CallArg {
                                        name: None,
                                        expr: iter_expr,
                                    }],
                                    inferred_ty: None,
                                })
                            }
                            None => iter_expr.node,
                        }
                    }
                    None => iter_expr.node,
                },
            };

            *expr = desugared;

            check_expr(tc_state, expr, loc, expected_ty, level, loop_stack)
        }

        ast::Expr::Record(ast::RecordExpr {
            fields,
            inferred_ty,
        }) => {
            assert!(inferred_ty.is_none());

            if fields.is_empty() {
                *inferred_ty = Some(Ty::unit());
                return (
                    unify_expected_ty(
                        Ty::unit(),
                        expected_ty,
                        tc_state.tys.tys.cons(),
                        tc_state.var_gen,
                        level,
                        loc,
                    ),
                    Default::default(),
                );
            }

            // TODO: For now only supporting named fields.
            let mut field_names: HashSet<&Id> = Default::default();
            for (field_name, _field_expr) in fields.iter() {
                if !field_names.insert(field_name) {
                    panic!(
                        "{}: Field name {} occurs multiple times in the record",
                        loc_display(loc),
                        field_name
                    );
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

            let mut record_fields: OrdMap<Id, Ty> = OrdMap::new();
            for (field_name, field_expr) in fields.iter_mut() {
                let expected_ty = expected_fields
                    .as_ref()
                    .and_then(|expected_fields| expected_fields.get(field_name));
                let (field_ty, _) = check_expr(
                    tc_state,
                    &mut field_expr.node,
                    &field_expr.loc,
                    expected_ty,
                    level,
                    loop_stack,
                );
                record_fields.insert(field_name.clone(), field_ty);
            }

            let ty = Ty::Anonymous {
                labels: record_fields,
                extension: None,
                kind: RecordOrVariant::Record,
                is_row: false,
            };

            *inferred_ty = Some(ty.clone());

            (
                unify_expected_ty(
                    ty,
                    expected_ty,
                    tc_state.tys.tys.cons(),
                    tc_state.var_gen,
                    level,
                    loc,
                ),
                Default::default(),
            )
        }

        ast::Expr::Variant(ast::VariantExpr { expr, inferred_ty }) => {
            assert!(inferred_ty.is_none());
            let (expr_ty, binders) =
                check_expr(tc_state, &mut expr.node, &expr.loc, None, level, loop_stack);
            let variant_ty = make_variant(tc_state, expr_ty, level, loc);
            *inferred_ty = Some(variant_ty.clone());
            (
                unify_expected_ty(
                    variant_ty,
                    expected_ty,
                    tc_state.tys.tys.cons(),
                    tc_state.var_gen,
                    level,
                    loc,
                ),
                binders,
            )
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

    let ast::MatchExpr {
        scrutinee,
        alts,
        inferred_ty,
    } = expr;

    assert!(inferred_ty.is_none());

    let (scrut_ty, _) = check_expr(
        tc_state,
        &mut scrutinee.node,
        &scrutinee.loc,
        None,
        level,
        loop_stack,
    );

    let mut rhs_tys: Vec<Ty> = Vec::with_capacity(alts.len());

    let mut alt_envs: Vec<HashMap<Id, Ty>> = Vec::with_capacity(alts.len());

    // Type check patterns first so that the coverage checker can assume patterns are well-typed.
    for ast::Alt {
        pat,
        guard: _, // checked below to use refined binders in guards
        rhs: _,
    } in alts.iter_mut()
    {
        tc_state.env.enter();

        let pat_ty = check_pat(tc_state, pat, level);
        unify(
            &pat_ty,
            &scrut_ty,
            tc_state.tys.tys.cons(),
            tc_state.var_gen,
            level,
            &pat.loc,
        );

        alt_envs.push(tc_state.env.exit());
    }

    let (exhaustive, info) = check_coverage(alts, &scrut_ty, tc_state, loc);

    for (arm_idx, arm) in alts.iter().enumerate() {
        if !info.is_useful(arm_idx as u32) {
            eprintln!("{}: Redundant branch", loc_display(&arm.pat.loc));
        }
    }

    if !exhaustive {
        eprintln!("{}: Unexhaustive pattern match", loc_display(loc));
    }

    for (alt_idx, (ast::Alt { pat, guard, rhs }, mut alt_scope)) in
        alts.iter_mut().zip(alt_envs.into_iter()).enumerate()
    {
        refine_binders(&mut alt_scope, &info.bound_vars[alt_idx], &pat.loc);

        tc_state.env.push_scope(alt_scope);

        // Guards are checked here to use refined binders in the guards.
        if let Some(guard) = guard {
            let (_, guard_binders) = check_expr(
                tc_state,
                &mut guard.node,
                &guard.loc,
                Some(&Ty::bool()),
                level,
                loop_stack,
            );
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
        inferred_ty,
    } = expr;

    assert!(inferred_ty.is_none());

    let mut branch_tys: Vec<Ty> = Vec::with_capacity(branches.len() + 1);

    for (cond, body) in branches {
        let (cond_ty, cond_binders) = check_expr(
            tc_state,
            &mut cond.node,
            &cond.loc,
            Some(&Ty::bool()),
            level,
            loop_stack,
        );
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
fn check_field_sel(
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
                    field_ty.clone(),
                    ast::Expr::FieldSel(ast::FieldSelExpr {
                        object: Box::new(object.clone()),
                        field: field.clone(),
                        user_ty_args: vec![],
                        inferred_ty: Some(field_ty),
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
                    field_ty.clone(),
                    ast::Expr::FieldSel(ast::FieldSelExpr {
                        object: Box::new(object.clone()),
                        field: field.clone(),
                        user_ty_args: vec![],
                        inferred_ty: Some(field_ty),
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
        (ty, args.into_iter().map(Ty::UVar).collect())
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

    let (mut args, ret, exceptions) = match method_ty {
        Ty::Fun {
            args,
            ret,
            exceptions,
        } => (args, ret, exceptions),

        _ => panic!(
            "{}: Type of method is not a function type: {:?}",
            loc_display(loc),
            method_ty
        ),
    };

    match &mut args {
        FunArgs::Positional(args) => {
            // Type arguments of the receiver already substituted for type parameters in
            // `select_method`. Drop 'self' argument.
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

    let ty = Ty::Fun {
        args,
        ret,
        exceptions,
    };

    (
        ty.clone(),
        ast::Expr::MethodSel(ast::MethodSelExpr {
            object: Box::new(object.clone()),
            object_ty: Some(object_ty.clone()),
            method_ty_id,
            method: field.clone(),
            ty_args: method_ty_args,
            inferred_ty: Some(ty),
        }),
    )
}

fn select_field(
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
        TyConDetails::Type(TypeDetails {
            cons,
            sum,
            value: _,
        }) if !sum => {
            assert_eq!(cons.len(), 1);
            let con_scheme = cons.values().next().unwrap();
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

pub(crate) fn make_variant(tc_state: &mut TcFunState, ty: Ty, level: u32, loc: &ast::Loc) -> Ty {
    let con = match ty.normalize(tc_state.tys.tys.cons()) {
        // Hack below: check first letter of the identifier to rigit type variables from type
        // constructors.
        //
        // Compiler doesn't have this issue as it has a `QVar` constructor.
        Ty::Con(con, _) if con.chars().next().unwrap().is_uppercase() => con,

        Ty::App(con, _, _) => con,

        ty => panic!(
            "{}: Type in variant is not a constructor: {}",
            loc_display(loc),
            ty
        ),
    };

    if con == "I8"
        || con == "U8"
        || con == "I16"
        || con == "U16"
        || con == "I32"
        || con == "U32"
        || con == "I64"
        || con == "U64"
    {
        panic!(
            "{}: Integers can't be made variants in the interpreter",
            loc_display(loc)
        );
    }

    let row_ext = tc_state
        .var_gen
        .new_var(level, Kind::Row(RecordOrVariant::Variant), loc.clone());

    Ty::Anonymous {
        labels: [(con, ty)].into_iter().collect(),
        extension: Some(Box::new(Ty::UVar(row_ext))),
        kind: RecordOrVariant::Variant,
        is_row: false,
    }
}

fn refine_binders(scope: &mut HashMap<Id, Ty>, binders: &HashMap<Id, HashSet<Ty>>, loc: &ast::Loc) {
    if cfg!(debug_assertions) {
        let scope_vars: HashSet<&Id> = scope.keys().collect();
        let binders_vars: HashSet<&Id> = binders.keys().collect();
        assert_eq!(scope_vars, binders_vars);
    }

    for (var, tys) in binders.iter() {
        // println!("{} --> {:?}", var, tys);
        // assert!(&tys.is_empty());

        if tys.len() == 1 {
            // println!("{} --> {}", var, tys.iter().next().unwrap().clone());
            scope.insert(var.clone(), tys.iter().next().unwrap().clone());
        } else {
            let mut labels: OrdMap<Id, Ty> = Default::default();
            let mut extension: Option<Box<Ty>> = None;

            for ty in tys.iter() {
                match ty {
                    Ty::Con(con, _) | Ty::App(con, _, _) => {
                        let old = labels.insert(con.clone(), ty.clone());
                        assert_eq!(old, None);
                    }

                    Ty::UVar(_) | Ty::QVar(_, _) => {
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
