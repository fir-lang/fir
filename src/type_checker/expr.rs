use crate::ast::{self, Id};
use crate::collections::{Map, Set};
use crate::interpolation::StringPart;
use crate::type_checker::convert::convert_ast_ty;
use crate::type_checker::pat::{check_pat, refine_pat_binders};
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
    loop_stack: &mut Vec<Option<Id>>,
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
                    tc_state.var_gen,
                    level,
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
                return unify_expected_ty(
                    ty,
                    expected_ty,
                    tc_state.tys.tys.cons(),
                    tc_state.var_gen,
                    level,
                    &expr.loc,
                );
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
            unify_expected_ty(
                ty,
                expected_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                &expr.loc,
            )
        }

        ast::Expr::Variant(ast::VariantExpr { id, args }) => {
            let mut arg_tys: Map<Id, Ty> =
                Map::with_capacity_and_hasher(args.len(), Default::default());

            for ast::Named { name, ref mut node } in args.iter_mut() {
                let name = match name {
                    Some(name) => name,
                    None => panic!(
                        "{}: Variant expression with unnamed args not supported yet",
                        loc_display(&expr.loc)
                    ),
                };
                let ty = check_expr(tc_state, node, None, level, loop_stack);
                let old = arg_tys.insert(name.clone(), ty);
                if old.is_some() {
                    panic!(
                        "{}: Variant expression with dupliate fields",
                        loc_display(&expr.loc)
                    );
                }
            }

            let record_ty = Ty::Anonymous {
                labels: arg_tys,
                extension: None,
                kind: RecordOrVariant::Record,
                is_row: false,
            };

            let ty = Ty::Anonymous {
                labels: [(id.clone(), record_ty)].into_iter().collect(),
                extension: Some(Box::new(Ty::Var(tc_state.var_gen.new_var(
                    level,
                    Kind::Row(RecordOrVariant::Variant),
                    expr.loc.clone(),
                )))),
                kind: RecordOrVariant::Variant,
                is_row: false,
            };

            unify_expected_ty(
                ty,
                expected_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                &expr.loc,
            )
        }

        ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field }) => {
            let ty = {
                let object_ty = check_expr(tc_state, object, None, level, loop_stack);

                // To be able to select a field or method of a type made precise via a unification
                // to an associated type, try to resolve predicates right before selecting the field
                // or method.
                *tc_state.preds = super::resolve_preds(
                    tc_state.context,
                    tc_state.tys,
                    take(tc_state.preds),
                    tc_state.var_gen,
                    level,
                );

                let field = field.clone();
                let expr_loc = expr.loc.clone();

                let ty_normalized = object_ty.normalize(tc_state.tys.tys.cons());
                match &ty_normalized {
                    Ty::Con(con) => {
                        check_field_select(tc_state, expr, con, &[], &field, &expr_loc, level)
                    }

                    Ty::App(con, args) => match args {
                        TyArgs::Positional(args) => {
                            check_field_select(tc_state, expr, con, args, &field, &expr_loc, level)
                        }
                        TyArgs::Named(_) => {
                            // Associated type arguments are only allowed in traits, sothe `con` must
                            // be a trait.
                            assert!(tc_state.tys.tys.get_con(con).unwrap().details.is_trait());
                            panic!("{}: Traits cannot have fields", loc_display(&object.loc))
                        }
                    },

                    Ty::Anonymous {
                        labels,
                        extension,
                        kind: RecordOrVariant::Record,
                        ..
                    } => {
                        let (labels, _) = crate::type_checker::row_utils::collect_rows(
                            tc_state.tys.tys.cons(),
                            &ty_normalized,
                            RecordOrVariant::Record,
                            labels,
                            extension.clone(),
                        );
                        match labels.get(&field) {
                            Some(field_ty) => field_ty.clone(),
                            None => panic!(
                                "{}: Record with fields {:?} does not have field {}",
                                loc_display(&object.loc),
                                labels.keys().collect::<Vec<_>>(),
                                field
                            ),
                        }
                    }

                    Ty::AssocTySelect { ty: _, assoc_ty: _ } => panic!(
                        "{}: Associated type select in field select expr",
                        loc_display(&object.loc)
                    ),

                    other @ (Ty::Var(_) | Ty::QVar(_) | Ty::Fun { .. } | Ty::Anonymous { .. }) => {
                        panic!(
                            "{}: Object {} in field selection does not have fields: {:?}",
                            loc_display(&object.loc),
                            other,
                            object_ty
                        )
                    }
                }
            };
            unify_expected_ty(
                ty,
                expected_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                &expr.loc,
            )
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
            unify_expected_ty(
                con_ty,
                expected_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                &expr.loc,
            )
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
            let fun_ty = check_expr(tc_state, fun, None, level, loop_stack);

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
                                let arg_ty = check_expr(
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
                                let arg_ty = check_expr(
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

                    unify_expected_ty(
                        *ret_ty,
                        expected_ty,
                        tc_state.tys.tys.cons(),
                        tc_state.var_gen,
                        level,
                        &expr.loc,
                    )
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
                        tc_state.var_gen,
                        level,
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
                        tc_state.var_gen,
                        level,
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
                        tc_state.var_gen,
                        level,
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
                        tc_state.var_gen,
                        level,
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
                        let expr_var =
                            tc_state
                                .var_gen
                                .new_var(level, Kind::Star, expr.loc.clone());
                        tc_state.preds.add(Pred {
                            ty_var: expr_var.clone(),
                            trait_: Ty::to_str_id(),
                            assoc_tys: Default::default(),
                            loc: expr.loc.clone(),
                        });
                        let part_ty =
                            check_expr(tc_state, expr, Some(&Ty::Var(expr_var)), level, loop_stack);
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
                                    ty_args: vec![tc_state.exceptions.clone()],
                                }),
                                loc: expr.loc.clone(),
                            }),
                            args: vec![],
                        });
                    }
                }
            }

            unify_expected_ty(
                Ty::str(),
                expected_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                &expr.loc,
            )
        }

        ast::Expr::Char(_) => unify_expected_ty(
            Ty::char(),
            expected_ty,
            tc_state.tys.tys.cons(),
            tc_state.var_gen,
            level,
            &expr.loc,
        ),

        ast::Expr::Self_ => match tc_state.env.get("self") {
            Some(self_ty) => unify_expected_ty(
                self_ty.clone(),
                expected_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                &expr.loc,
            ),
            None => panic!("{}: Unbound self", loc_display(&expr.loc)),
        },

        ast::Expr::BinOp(ast::BinOpExpr { left, right, op }) => {
            let method = match op {
                ast::BinOp::And | ast::BinOp::Or => {
                    let bool_ty = Ty::Con("Bool".into());
                    check_expr(tc_state, left, Some(&bool_ty), level, loop_stack);
                    check_expr(tc_state, right, Some(&bool_ty), level, loop_stack);
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

            check_expr(tc_state, expr, expected_ty, level, loop_stack)
        }

        ast::Expr::UnOp(ast::UnOpExpr { op, expr: arg }) => match op {
            ast::UnOp::Not => check_expr(tc_state, arg, Some(&Ty::bool()), level, loop_stack),

            ast::UnOp::Neg => {
                let desugared = ast::L {
                    loc: expr.loc.clone(),
                    node: ast::Expr::Call(ast::CallExpr {
                        fun: Box::new(ast::L {
                            loc: arg.loc.clone(),
                            node: ast::Expr::FieldSelect(ast::FieldSelectExpr {
                                object: arg.clone(),
                                field: SmolStr::new_static("__neg"),
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
                return unify_expected_ty(
                    Ty::unit(),
                    expected_ty,
                    tc_state.tys.tys.cons(),
                    tc_state.var_gen,
                    level,
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

            let mut record_fields: Map<Id, Ty> = Default::default();
            for field in fields.iter_mut() {
                let field_name = field.name.as_ref().unwrap();
                let expected_ty = expected_fields
                    .as_ref()
                    .and_then(|expected_fields| expected_fields.get(field_name));
                let field_ty =
                    check_expr(tc_state, &mut field.node, expected_ty, level, loop_stack);
                record_fields.insert(field_name.clone(), field_ty);
            }

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
            )
        }

        ast::Expr::Return(expr) => {
            let return_ty = tc_state.return_ty.clone();
            check_expr(tc_state, expr, Some(&return_ty), level, loop_stack);
            expected_ty.cloned().unwrap_or_else(|| {
                Ty::Var(
                    tc_state
                        .var_gen
                        .new_var(level, Kind::Star, expr.loc.clone()),
                )
            })
        }

        ast::Expr::Match(ast::MatchExpr { scrutinee, alts }) => {
            let scrut_ty = check_expr(tc_state, scrutinee, None, level, loop_stack);

            let mut rhs_tys: Vec<Ty> = Vec::with_capacity(alts.len());

            let mut covered_pats = crate::type_checker::pat_coverage::PatCoverage::new();

            for ast::Alt {
                pattern,
                guard,
                rhs,
            } in alts
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

                refine_pat_binders(tc_state, &scrut_ty, pattern, &covered_pats);

                if let Some(guard) = guard {
                    check_expr(tc_state, guard, Some(&Ty::bool()), level, loop_stack);
                }

                rhs_tys.push(check_stmts(tc_state, rhs, None, level, loop_stack));

                tc_state.env.exit();

                if guard.is_none() {
                    covered_pats.add(&pattern.node);
                }
            }

            let exhaustive = covered_pats.is_exhaustive(&scrut_ty, tc_state, &expr.loc);
            if !exhaustive {
                println!("{}: Unexhaustive pattern match", loc_display(&expr.loc));
            }

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

            unify_expected_ty(
                rhs_tys.pop().unwrap(),
                expected_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                &expr.loc,
            )
        }

        ast::Expr::If(ast::IfExpr {
            branches,
            else_branch,
        }) => {
            let mut branch_tys: Vec<Ty> = Vec::with_capacity(branches.len() + 1);

            for (cond, body) in branches {
                let cond_ty = check_expr(tc_state, cond, Some(&Ty::bool()), level, loop_stack);
                unify(
                    &cond_ty,
                    &Ty::bool(),
                    tc_state.tys.tys.cons(),
                    tc_state.var_gen,
                    level,
                    &expr.loc,
                );

                let body_ty = check_stmts(tc_state, body, expected_ty, level, loop_stack);

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

            branch_tys.pop().unwrap()
        }

        ast::Expr::Fn(ast::FnExpr { sig, body, idx }) => {
            assert!(sig.type_params.is_empty());
            assert_eq!(*idx, 0);

            tc_state.env.enter(); // for term params

            let ret_ty = match &sig.return_ty {
                Some(ty) => convert_ast_ty(&tc_state.tys.tys, &ty.node, &ty.loc),
                None => Ty::Var(
                    tc_state
                        .var_gen
                        .new_var(level + 1, Kind::Star, expr.loc.clone()),
                ),
            };

            let exceptions = match &sig.exceptions {
                Some(exc) => convert_ast_ty(&tc_state.tys.tys, &exc.node, &exc.loc),
                None => {
                    let row = tc_state.var_gen.new_var(
                        level + 1,
                        Kind::Row(RecordOrVariant::Variant),
                        expr.loc.clone(),
                    );
                    Ty::Anonymous {
                        labels: Default::default(),
                        extension: Some(Box::new(Ty::Var(row))),
                        kind: RecordOrVariant::Variant,
                        is_row: false,
                    }
                }
            };

            let mut param_tys: Vec<Ty> = Vec::with_capacity(sig.params.len());
            for (param_name, param_ty) in &sig.params {
                let param_ty = convert_ast_ty(&tc_state.tys.tys, &param_ty.node, &expr.loc);
                tc_state.env.insert(param_name.clone(), param_ty.clone());
                param_tys.push(param_ty.clone());
            }

            let old_ret_ty = replace(&mut tc_state.return_ty, ret_ty.clone());
            let old_exceptions = replace(&mut tc_state.exceptions, exceptions.clone());
            let old_preds = take(tc_state.preds);

            check_stmts(tc_state, body, Some(&ret_ty), 0, &mut Vec::new());

            let new_preds = replace(tc_state.preds, old_preds);
            assert!(new_preds.into_preds().is_empty());

            let exceptions = replace(&mut tc_state.exceptions, old_exceptions);
            let ret_ty = replace(&mut tc_state.return_ty, old_ret_ty);

            tc_state.env.exit();

            let ty = Ty::Fun {
                args: FunArgs::Positional(param_tys),
                ret: Box::new(ret_ty),
                exceptions: Some(Box::new(exceptions)),
            };

            unify_expected_ty(
                ty,
                expected_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                &expr.loc,
            )
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

    match select_field(tc_state, ty_con, ty_args, &field_select.field, loc) {
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
                    Ty::Fun {
                        mut args,
                        ret,
                        exceptions,
                    } => {
                        match &mut args {
                            FunArgs::Positional(args) => {
                                args.remove(0);
                            }
                            FunArgs::Named(_) => panic!(),
                        }
                        Ty::Fun {
                            args,
                            ret,
                            exceptions,
                        }
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
        TyConDetails::Type(TypeDetails { cons }) => match cons.len() {
            1 => {
                let con_name = cons[0].name.as_ref().unwrap_or(&ty_con.id);
                let con_scheme = tc_state.tys.top_schemes.get(con_name)?;
                let con_ty = con_scheme.instantiate_with_tys(ty_args);

                match con_ty {
                    Ty::Fun {
                        args: FunArgs::Named(fields),
                        ret: _,
                        exceptions: _,
                    } => Some(fields.get(field)?.clone()),
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
        .map(|(qvar, _)| qvar.clone())
        .collect();

    for (quantified_var, ty_arg) in substituted_quantified_vars.iter().zip(ty_args.iter()) {
        scheme = scheme.subst(quantified_var, ty_arg, loc);
    }

    Some(scheme)
}
