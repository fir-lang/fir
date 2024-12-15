use crate::ast::{self, Id};
use crate::collections::{Map, Set};
use crate::interpolation::StringPart;
use crate::type_checker::pat::check_pat;
use crate::type_checker::stmt::check_stmts;
use crate::type_checker::ty::*;
use crate::type_checker::unification::{unify, unify_expected_ty};
use crate::type_checker::{loc_display, PgmTypes, TcFunState};

use std::mem::{replace, take};

use smol_str::SmolStr;

pub(super) fn check_expr(
    tc_state: &mut TcFunState,
    expr: &mut ast::L<ast::Expr>,
    expected_ty: Option<&Ty>,
    level: u32,
    loop_depth: u32,
) -> Ty {
    match &mut expr.node {
        ast::Expr::Var(ast::VarExpr { id: var, ty_args }) => {
            debug_assert!(ty_args.is_empty());

            // Check if local.
            if let Some(ty) = tc_state.env.get(var) {
                return unify_expected_ty(
                    ty.clone(),
                    expected_ty,
                    tc_state.tys.tys.cons(),
                    &expr.loc,
                );
            }

            if let Some(scheme) = tc_state.tys.top_schemes.get(var) {
                let (ty, ty_args) =
                    scheme.instantiate(level, tc_state.var_gen, tc_state.preds, &expr.loc);
                expr.node = ast::Expr::Var(ast::VarExpr {
                    id: var.clone(),
                    ty_args: ty_args.into_iter().map(Ty::Var).collect(),
                });
                return unify_expected_ty(ty, expected_ty, tc_state.tys.tys.cons(), &expr.loc);
            }

            panic!("{}: Unbound variable {}", loc_display(&expr.loc), var);
        }

        ast::Expr::Constr(ast::ConstrExpr { id: con, ty_args }) => {
            assert!(ty_args.is_empty());
            let scheme = tc_state.tys.top_schemes.get(con).unwrap_or_else(|| {
                panic!("{}: Unknown constructor {}", loc_display(&expr.loc), con)
            });
            let (ty, ty_args) =
                scheme.instantiate(level, tc_state.var_gen, tc_state.preds, &expr.loc);
            expr.node = ast::Expr::Constr(ast::ConstrExpr {
                id: con.clone(),
                ty_args: ty_args.into_iter().map(Ty::Var).collect(),
            });
            unify_expected_ty(ty, expected_ty, tc_state.tys.tys.cons(), &expr.loc)
        }

        ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field }) => {
            let ty = {
                let object_ty = check_expr(tc_state, object, None, level, loop_depth);

                // To be able to select a field or method of a type made precise via a unification
                // to an associated type, try to resolve predicates right before selecting the field
                // or method.
                *tc_state.preds =
                    super::resolve_preds(tc_state.context, tc_state.tys, take(tc_state.preds));

                let field = field.clone();
                let expr_loc = expr.loc.clone();

                match object_ty.normalize(tc_state.tys.tys.cons()) {
                    Ty::Con(con) => {
                        check_field_select(tc_state, expr, &con, &[], &field, &expr_loc, level)
                    }

                    Ty::App(con, args) => match args {
                        TyArgs::Positional(args) => check_field_select(
                            tc_state, expr, &con, &args, &field, &expr_loc, level,
                        ),
                        TyArgs::Named(_) => {
                            // Associated type arguments are only allowed in traits, sothe `con` must
                            // be a trait.
                            assert!(tc_state.tys.tys.get_con(&con).unwrap().details.is_trait());
                            panic!("{}: Traits cannot have fields", loc_display(&object.loc))
                        }
                    },

                    Ty::Record(fields) => match fields.get(&field) {
                        Some(field_ty) => field_ty.clone(),
                        None => panic!(
                            "{}: Record with fields {:?} does not have field {}",
                            loc_display(&object.loc),
                            fields.keys().collect::<Vec<_>>(),
                            field
                        ),
                    },

                    Ty::AssocTySelect { ty: _, assoc_ty: _ } => panic!(
                        "{}: Associated type select in fiel select expr",
                        loc_display(&object.loc)
                    ),

                    other @ (Ty::Var(_) | Ty::QVar(_) | Ty::Fun(_, _) | Ty::FunNamedArgs(_, _)) => {
                        panic!(
                            "{}: Object {} in field selection does not have fields: {:?}",
                            loc_display(&object.loc),
                            other,
                            object_ty
                        )
                    }
                }
            };
            unify_expected_ty(ty, expected_ty, tc_state.tys.tys.cons(), &expr.loc)
        }

        ast::Expr::MethodSelect(_) => panic!("MethodSelect in type checker"),

        ast::Expr::ConstrSelect(ast::ConstrSelectExpr {
            ty,
            constr,
            ty_args,
        }) => {
            assert!(ty_args.is_empty());
            let scheme = tc_state
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
                });
            let (con_ty, con_ty_args) =
                scheme.instantiate(level, tc_state.var_gen, tc_state.preds, &expr.loc);
            expr.node = ast::Expr::ConstrSelect(ast::ConstrSelectExpr {
                ty: ty.clone(),
                constr: constr.clone(),
                ty_args: con_ty_args.into_iter().map(Ty::Var).collect(),
            });
            unify_expected_ty(con_ty, expected_ty, tc_state.tys.tys.cons(), &expr.loc)
        }

        ast::Expr::AssocFnSelect(ast::AssocFnSelectExpr {
            ty,
            member,
            ty_args,
        }) => {
            assert!(ty_args.is_empty());
            let scheme = tc_state
                .tys
                .associated_fn_schemes
                .get(ty)
                .unwrap_or_else(|| panic!("{}: Unknown type {}", loc_display(&expr.loc), ty))
                .get(member)
                .or_else(|| tc_state.tys.method_schemes.get(ty).unwrap().get(member))
                .unwrap_or_else(|| {
                    panic!(
                        "{}: Type {} does not have associated function {}",
                        loc_display(&expr.loc),
                        ty,
                        member
                    )
                });
            let (method_ty, method_ty_args) =
                scheme.instantiate(level, tc_state.var_gen, tc_state.preds, &expr.loc);
            expr.node = ast::Expr::AssocFnSelect(ast::AssocFnSelectExpr {
                ty: ty.clone(),
                member: member.clone(),
                ty_args: method_ty_args.into_iter().map(Ty::Var).collect(),
            });
            method_ty
        }

        ast::Expr::Call(ast::CallExpr { fun, args }) => {
            let fun_ty = check_expr(tc_state, fun, None, level, loop_depth);

            match fun_ty.normalize(tc_state.tys.tys.cons()) {
                Ty::Fun(param_tys, ret_ty) => {
                    if param_tys.len() != args.len() {
                        panic!(
                            "{}: Function with arity {} is passed {} args",
                            loc_display(&expr.loc),
                            param_tys.len(),
                            args.len()
                        );
                    }

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
                        let arg_ty =
                            check_expr(tc_state, &mut arg.expr, Some(param_ty), level, loop_depth);
                        arg_tys.push(arg_ty);
                    }
                    unify_expected_ty(*ret_ty, expected_ty, tc_state.tys.tys.cons(), &expr.loc)
                }

                Ty::FunNamedArgs(param_tys, ret_ty) => {
                    if param_tys.len() != args.len() {
                        panic!(
                            "{}: Function with arity {} is passed {} args",
                            loc_display(&expr.loc),
                            param_tys.len(),
                            args.len()
                        );
                    }

                    for arg in args.iter() {
                        if arg.name.is_none() {
                            panic!(
                                "{}: Positional argument applied to function that expects named arguments",
                                loc_display(&expr.loc),
                            );
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
                        let arg_ty =
                            check_expr(tc_state, &mut arg.expr, Some(param_ty), level, loop_depth);
                        unify(&arg_ty, param_ty, tc_state.tys.tys.cons(), &expr.loc);
                    }

                    unify_expected_ty(*ret_ty, expected_ty, tc_state.tys.tys.cons(), &expr.loc)
                }

                _ => panic!(
                    "{}: Function in function application is not a function: {:?}",
                    loc_display(&expr.loc),
                    fun_ty,
                ),
            }
        }

        ast::Expr::Range(ast::RangeExpr { .. }) => {
            panic!(
                "{}: Range expressions are currently only allowed in `for` loops",
                loc_display(&expr.loc)
            );
        }

        ast::Expr::Int(ast::IntExpr {
            text,
            suffix,
            radix,
            parsed,
        }) => {
            let kind: ast::IntKind = suffix.unwrap_or_else(|| {
                match expected_ty.map(|ty| ty.normalize(tc_state.tys.tys.cons())) {
                    Some(Ty::Con(con)) if con == "I8" => ast::IntKind::I8,
                    Some(Ty::Con(con)) if con == "U8" => ast::IntKind::U8,
                    Some(Ty::Con(con)) if con == "I32" => ast::IntKind::I32,
                    Some(Ty::Con(con)) if con == "U32" => ast::IntKind::U32,

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
                    unify_expected_ty(
                        Ty::Con("I8".into()),
                        expected_ty,
                        tc_state.tys.tys.cons(),
                        &expr.loc,
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
                    unify_expected_ty(
                        Ty::Con("U8".into()),
                        expected_ty,
                        tc_state.tys.tys.cons(),
                        &expr.loc,
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
                    unify_expected_ty(
                        Ty::Con("I32".into()),
                        expected_ty,
                        tc_state.tys.tys.cons(),
                        &expr.loc,
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
                    unify_expected_ty(
                        Ty::Con("U32".into()),
                        expected_ty,
                        tc_state.tys.tys.cons(),
                        &expr.loc,
                    )
                }
            }
        }

        ast::Expr::String(parts) => {
            for part in parts {
                match part {
                    StringPart::Str(_) => continue,
                    StringPart::Expr(expr) => {
                        let expr_var = tc_state.var_gen.new_var(level, expr.loc.clone());
                        tc_state.preds.add(Pred {
                            ty_var: expr_var.clone(),
                            trait_: Ty::to_str_id(),
                            assoc_tys: Default::default(),
                            loc: expr.loc.clone(),
                        });
                        let part_ty =
                            check_expr(tc_state, expr, Some(&Ty::Var(expr_var)), level, loop_depth);
                        let expr_node = replace(&mut expr.node, ast::Expr::Self_);
                        expr.node = ast::Expr::Call(ast::CallExpr {
                            fun: Box::new(ast::L {
                                node: ast::Expr::MethodSelect(ast::MethodSelectExpr {
                                    object: Box::new(ast::L {
                                        node: expr_node,
                                        loc: expr.loc.clone(),
                                    }),
                                    object_ty: Some(part_ty),
                                    method: SmolStr::new_static("toStr"),
                                    ty_args: vec![],
                                }),
                                loc: expr.loc.clone(),
                            }),
                            args: vec![],
                        });
                    }
                }
            }

            unify_expected_ty(Ty::str(), expected_ty, tc_state.tys.tys.cons(), &expr.loc)
        }

        ast::Expr::Char(_) => {
            unify_expected_ty(Ty::char(), expected_ty, tc_state.tys.tys.cons(), &expr.loc)
        }

        ast::Expr::Self_ => match tc_state.env.get("self") {
            Some(self_ty) => unify_expected_ty(
                self_ty.clone(),
                expected_ty,
                tc_state.tys.tys.cons(),
                &expr.loc,
            ),
            None => panic!("{}: Unbound self", loc_display(&expr.loc)),
        },

        ast::Expr::BinOp(ast::BinOpExpr { left, right, op }) => {
            let method = match op {
                ast::BinOp::And | ast::BinOp::Or => {
                    let bool_ty = Ty::Con("Bool".into());
                    check_expr(tc_state, left, Some(&bool_ty), level, loop_depth);
                    check_expr(tc_state, right, Some(&bool_ty), level, loop_depth);
                    return bool_ty;
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
                        }),
                    }),
                    args: vec![ast::CallArg {
                        name: None,
                        expr: (**right).clone(),
                    }],
                }),
            };

            *expr = desugared;

            check_expr(tc_state, expr, expected_ty, level, loop_depth)
        }

        ast::Expr::UnOp(ast::UnOpExpr { op, expr }) => match op {
            ast::UnOp::Not => check_expr(tc_state, expr, Some(&Ty::bool()), level, loop_depth),
        },

        ast::Expr::Record(fields) => {
            if fields.is_empty() {
                return unify_expected_ty(
                    Ty::unit(),
                    expected_ty,
                    tc_state.tys.tys.cons(),
                    &expr.loc,
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
            let expected_fields = expected_ty.map(|expected_ty| {
                match expected_ty.normalize(tc_state.tys.tys.cons()) {
                    Ty::Record(expected_fields) => expected_fields,
                    other => panic!(
                        "{}: Record expression expected to have type {:?}",
                        loc_display(&expr.loc),
                        other
                    ),
                }
            });

            if let Some(expected_fields) = &expected_fields {
                let expected_field_names: Set<&Id> = expected_fields.keys().collect();
                if expected_field_names != field_names {
                    panic!(
                        "{}: Record expected to have fields {:?}, but it has fields {:?}",
                        loc_display(&expr.loc),
                        expected_field_names,
                        field_names
                    );
                }
            }

            let mut record_ty: Map<Id, Ty> = Default::default();
            for field in fields.iter_mut() {
                let field_name = field.name.as_ref().unwrap();
                let expected_ty = expected_fields
                    .as_ref()
                    .map(|expected_fields| expected_fields.get(field_name).unwrap());
                let field_ty =
                    check_expr(tc_state, &mut field.node, expected_ty, level, loop_depth);
                record_ty.insert(field_name.clone(), field_ty);
            }

            unify_expected_ty(
                Ty::Record(record_ty),
                expected_ty,
                tc_state.tys.tys.cons(),
                &expr.loc,
            )
        }

        ast::Expr::Return(expr) => {
            check_expr(tc_state, expr, Some(tc_state.return_ty), level, loop_depth);
            expected_ty.cloned().unwrap_or_else(Ty::unit)
        }

        ast::Expr::Match(ast::MatchExpr { scrutinee, alts }) => {
            let scrut_ty = check_expr(tc_state, scrutinee, None, level, loop_depth);

            let mut rhs_tys: Vec<Ty> = Vec::with_capacity(alts.len());

            for ast::Alt {
                pattern,
                guard,
                rhs,
            } in alts
            {
                let pat_ty = check_pat(tc_state, pattern, level);
                unify(&pat_ty, &scrut_ty, tc_state.tys.tys.cons(), &pattern.loc);

                if let Some(guard) = guard {
                    check_expr(tc_state, guard, Some(&Ty::bool()), level, loop_depth);
                }

                rhs_tys.push(check_stmts(tc_state, rhs, None, level, loop_depth));
            }

            for rhs_tys in rhs_tys.windows(2) {
                unify(&rhs_tys[0], &rhs_tys[1], tc_state.tys.tys.cons(), &expr.loc);
            }

            unify_expected_ty(
                rhs_tys.pop().unwrap(),
                expected_ty,
                tc_state.tys.tys.cons(),
                &expr.loc,
            )
        }

        ast::Expr::If(ast::IfExpr {
            branches,
            else_branch,
        }) => {
            let mut branch_tys: Vec<Ty> = Vec::with_capacity(branches.len() + 1);

            for (cond, body) in branches {
                let cond_ty = check_expr(tc_state, cond, Some(&Ty::bool()), level, loop_depth);
                unify(&cond_ty, &Ty::bool(), tc_state.tys.tys.cons(), &expr.loc);

                let body_ty = check_stmts(tc_state, body, expected_ty, level, loop_depth);

                branch_tys.push(body_ty);
            }

            match else_branch {
                Some(else_body) => {
                    let body_ty = check_stmts(tc_state, else_body, expected_ty, level, loop_depth);
                    branch_tys.push(body_ty);
                }
                None => {
                    // A bit hacky: ensure that without an else branch the expression returns unit.
                    branch_tys.push(Ty::unit());
                }
            }

            // When expected type is available, unify with it for better errors.
            match expected_ty {
                Some(expected_ty) => {
                    for ty in &branch_tys {
                        unify(ty, expected_ty, tc_state.tys.tys.cons(), &expr.loc);
                    }
                }
                None => {
                    for ty_pair in branch_tys.windows(2) {
                        unify(&ty_pair[0], &ty_pair[1], tc_state.tys.tys.cons(), &expr.loc);
                    }
                }
            }

            branch_tys.pop().unwrap()
        }

        ast::Expr::As(ast::AsExpr {
            expr,
            expr_ty,
            target_ty,
        }) => {
            assert_eq!(expr_ty, &None);
            let expr_ty_ = check_expr(tc_state, expr, None, level, loop_depth)
                .normalize(tc_state.tys.tys.cons());
            let as_ty = match expr_ty_ {
                Ty::Con(id) if id.as_str() == "I8" => ast::AsExprTy::I8,
                Ty::Con(id) if id.as_str() == "U8" => ast::AsExprTy::U8,
                Ty::Con(id) if id.as_str() == "I32" => ast::AsExprTy::I32,
                Ty::Con(id) if id.as_str() == "U32" => ast::AsExprTy::U32,
                other => panic!(
                    "{}: Source of `as` expression should have a numeric type, but it is {}",
                    loc_display(&expr.loc),
                    other
                ),
            };
            *expr_ty = Some(as_ty);
            match target_ty {
                ast::AsExprTy::U8 => Ty::u8(),
                ast::AsExprTy::I8 => Ty::i8(),
                ast::AsExprTy::U32 => Ty::u32(),
                ast::AsExprTy::I32 => Ty::i32(),
            }
        }
    }
}

/// Check a `FieldSelect` expr.
///
/// `object` must be an `Expr::FieldSelect`.
fn check_field_select(
    tc_state: &mut TcFunState,
    object: &mut ast::L<ast::Expr>,
    ty_con: &Id,
    ty_args: &[Ty],
    field: &Id,
    loc: &ast::Loc,
    level: u32,
) -> Ty {
    let field_select = match &mut object.node {
        ast::Expr::FieldSelect(field_select) => field_select,
        _ => panic!("BUG: Expression in `check_field_select` is not a `FieldSelect`"),
    };

    match select_field(ty_con, ty_args, &field_select.field, loc, tc_state.tys) {
        Some(ty) => ty,
        None => match select_method(ty_con, ty_args, &field_select.field, tc_state.tys, loc) {
            Some(scheme) => {
                let (method_ty, method_ty_args) =
                    scheme.instantiate(level, tc_state.var_gen, tc_state.preds, loc);
                // Instantiates an associated function.
                object.node = ast::Expr::MethodSelect(ast::MethodSelectExpr {
                    // Replace detached field_select field with some random expr to avoid
                    // cloning.
                    object: Box::new(replace(
                        &mut field_select.object,
                        ast::L {
                            loc: ast::Loc::dummy(),
                            node: ast::Expr::Self_,
                        },
                    )),
                    object_ty: Some(if ty_args.is_empty() {
                        Ty::Con(ty_con.clone())
                    } else {
                        Ty::App(ty_con.clone(), TyArgs::Positional(ty_args.to_vec()))
                    }),
                    method: field_select.field.clone(),
                    ty_args: method_ty_args.into_iter().map(Ty::Var).collect(),
                });

                // Type arguments of the receiver already substituted for type parameters in
                // `select_method`. Drop 'self' argument.
                match method_ty {
                    Ty::Fun(mut args, ret) => {
                        args.remove(0);
                        Ty::Fun(args, ret)
                    }
                    _ => panic!(
                        "{}: Type of method is not a function type: {:?}",
                        loc_display(loc),
                        method_ty
                    ),
                }
            }
            None => panic!(
                "{}: Type {} does not have field or method {}",
                loc_display(loc),
                ty_con,
                field
            ),
        },
    }
}

/// Try to select a field.
pub(super) fn select_field(
    ty_con: &Id,
    ty_args: &[Ty],
    field: &Id,
    loc: &ast::Loc,
    tys: &PgmTypes,
) -> Option<Ty> {
    let ty_con = tys
        .tys
        .get_con(ty_con)
        .unwrap_or_else(|| panic!("{}: Unknown type {}", loc_display(loc), ty_con));

    assert_eq!(ty_con.ty_params.len(), ty_args.len());

    match &ty_con.details {
        TyConDetails::Type(TypeDetails { cons }) => match cons.len() {
            1 => {
                let con_name = cons[0].name.as_ref().unwrap_or(&ty_con.id);
                let con_scheme = tys.top_schemes.get(con_name)?;
                let con_ty = con_scheme.instantiate_with_tys(ty_args);

                match con_ty {
                    Ty::FunNamedArgs(fields, _) => Some(fields.get(field)?.clone()),
                    _ => None,
                }
            }

            _ => None,
        },

        TyConDetails::Trait(_) => {
            // Stand-alone `trait.method` can't work, we need to look at the arguments.
            // Ignore this for now, we probably won't need it.
            todo!(
                "{}: FieldSelect expression selecting a trait method without receiver",
                loc_display(loc)
            );
        }

        TyConDetails::Synonym(_) => {
            panic!("{}: Type synonym in select_field", loc_display(loc));
        }
    }
}

/// Try to select a method. Does not select associated functions.
fn select_method(
    ty_con: &Id,
    ty_args: &[Ty],
    field: &Id,
    tys: &PgmTypes,
    loc: &ast::Loc,
) -> Option<Scheme> {
    let ty_con = tys.tys.get_con(ty_con).unwrap();
    assert_eq!(ty_con.ty_params.len(), ty_args.len());

    let ty_methods = tys.method_schemes.get(&ty_con.id)?;
    let mut scheme = ty_methods.get(field)?.clone();

    // Replace the first type parameters of the scheme with `ty_args`.
    assert!(ty_args.len() <= scheme.quantified_vars.len());

    let substituted_quantified_vars: Vec<Id> = scheme
        .quantified_vars
        .iter()
        .take(ty_args.len())
        .map(|(id, _)| id.clone())
        .collect();

    for (quantified_var, ty_arg) in substituted_quantified_vars.iter().zip(ty_args.iter()) {
        scheme = scheme.subst(quantified_var, ty_arg, loc);
    }

    Some(scheme)
}
