use crate::ast;
use crate::collections::{Map, Set};
use crate::interpolation::StringPart;
use crate::scope_map::ScopeMap;
use crate::type_checker::pat::check_pat;
use crate::type_checker::stmt::check_stmts;
use crate::type_checker::ty::*;
use crate::type_checker::unification::{unify, unify_expected_ty};
use crate::type_checker::{loc_string, PgmTypes};

use smol_str::SmolStr;

pub(super) fn check_expr(
    expr: &ast::L<ast::Expr>,
    expected_ty: Option<&Ty>,
    return_ty: &Ty,
    level: u32,
    env: &mut ScopeMap<Id, Ty>,
    var_gen: &mut TyVarGen,
    tys: &PgmTypes,
    preds: &mut PredSet,
) -> Ty {
    match &expr.node {
        ast::Expr::Var(var) => {
            // Check if local.
            if let Some(ty) = env.get(var) {
                return unify_expected_ty(ty.clone(), expected_ty, &tys.cons, &expr.loc);
            }

            if let Some(scheme) = tys.top_schemes.get(var) {
                let ty = scheme.instantiate(level, var_gen, preds, &expr.loc);
                return unify_expected_ty(ty, expected_ty, &tys.cons, &expr.loc);
            }

            panic!("{}: Unbound variable {}", loc_string(&expr.loc), var);
        }

        ast::Expr::UpperVar(_) => todo!(),

        ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field }) => {
            let object_ty = check_expr(object, None, return_ty, level, env, var_gen, tys, preds);

            let ty = match object_ty.normalize(&tys.cons) {
                Ty::Con(con) => {
                    check_field_select(&con, &[], field, &expr.loc, tys, level, var_gen, preds)
                }

                Ty::App(con, args) => match args {
                    TyArgs::Positional(args) => check_field_select(
                        &con, &args, field, &expr.loc, tys, level, var_gen, preds,
                    ),
                    TyArgs::Named(_) => {
                        // Associated type arguments are only allowed in traits, sothe `con` must
                        // be a trait.
                        assert!(tys.cons.get(&con).unwrap().details.is_trait());
                        panic!("{}: Traits cannot have fields", loc_string(&object.loc))
                    }
                },

                Ty::Record(fields) => match fields.get(field) {
                    Some(field_ty) => field_ty.clone(),
                    None => panic!(
                        "{}: Record with fields {:?} does not have field {}",
                        loc_string(&object.loc),
                        fields.keys().collect::<Vec<_>>(),
                        field
                    ),
                },

                Ty::AssocTySelect { ty: _, assoc_ty: _ } => panic!(
                    "{}: Associated type select in fiel select expr",
                    loc_string(&object.loc)
                ),

                Ty::Var(_) | Ty::QVar(_) | Ty::Fun(_, _) | Ty::FunNamedArgs(_, _) => panic!(
                    "{}: Object in field selection does not have fields: {:?}",
                    loc_string(&object.loc),
                    object_ty
                ),
            };

            unify_expected_ty(ty, expected_ty, &tys.cons, &expr.loc)
        }

        ast::Expr::ConstrSelect(ast::ConstrSelectExpr { ty, constr }) => {
            let scheme = tys
                .associated_schemes
                .get(ty)
                .unwrap_or_else(|| {
                    panic!(
                        "{}: Type {} is not in type environment",
                        loc_string(&expr.loc),
                        ty
                    )
                })
                .get(constr)
                .unwrap_or_else(|| {
                    panic!(
                        "{}: Type {} does not have the constructor {}",
                        loc_string(&expr.loc),
                        ty,
                        constr
                    )
                });
            scheme.instantiate(level, var_gen, preds, &expr.loc)
        }

        ast::Expr::Call(ast::CallExpr { fun, args }) => {
            let fun_ty = check_expr(fun, None, return_ty, level, env, var_gen, tys, preds);

            // TODO: Handle passing self when `fun` is a `FieldSelect`.
            match fun_ty {
                Ty::Fun(param_tys, ret_ty) => {
                    if param_tys.len() != args.len() {
                        panic!(
                            "{}: Function with arity {} is passed {} args",
                            loc_string(&expr.loc),
                            param_tys.len(),
                            args.len()
                        );
                    }

                    for arg in args {
                        if arg.name.is_some() {
                            panic!(
                                "{}: Named argument applied to function that expects positional arguments",
                                loc_string(&expr.loc),
                            );
                        }
                    }

                    let mut arg_tys: Vec<Ty> = Vec::with_capacity(args.len());
                    for (param_ty, arg) in param_tys.iter().zip(args.iter()) {
                        let arg_ty = check_expr(
                            &arg.expr,
                            Some(param_ty),
                            return_ty,
                            level,
                            env,
                            var_gen,
                            tys,
                            preds,
                        );
                        arg_tys.push(arg_ty);
                    }

                    for (param_ty, arg_ty) in param_tys.iter().zip(arg_tys.iter()) {
                        unify(param_ty, arg_ty, &tys.cons, &expr.loc);
                    }

                    unify_expected_ty(*ret_ty, expected_ty, &tys.cons, &expr.loc)
                }

                Ty::FunNamedArgs(param_tys, ret_ty) => {
                    if param_tys.len() != args.len() {
                        panic!(
                            "{}: Function with arity {} is passed {} args",
                            loc_string(&expr.loc),
                            param_tys.len(),
                            args.len()
                        );
                    }

                    for arg in args {
                        if arg.name.is_none() {
                            panic!(
                                "{}: Positional argument applied to function that expects named arguments",
                                loc_string(&expr.loc),
                            );
                        }
                    }

                    let param_names: Set<&SmolStr> = param_tys.keys().collect();
                    let arg_names: Set<&SmolStr> =
                        args.iter().map(|arg| arg.name.as_ref().unwrap()).collect();

                    if param_names != arg_names {
                        panic!(
                            "{}: Function expects arguments with names {:?}, but passed {:?}",
                            loc_string(&expr.loc),
                            param_names,
                            arg_names
                        );
                    }

                    for arg in args {
                        let arg_name: &SmolStr = arg.name.as_ref().unwrap();
                        let param_ty: &Ty = param_tys.get(arg_name).unwrap();
                        let arg_ty = check_expr(
                            &arg.expr,
                            Some(param_ty),
                            return_ty,
                            level,
                            env,
                            var_gen,
                            tys,
                            preds,
                        );
                        unify(&arg_ty, param_ty, &tys.cons, &expr.loc);
                    }

                    unify_expected_ty(*ret_ty, expected_ty, &tys.cons, &expr.loc)
                }

                _ => panic!(
                    "{}: Function in function application is not a function: {:?}",
                    loc_string(&expr.loc),
                    fun_ty,
                ),
            }
        }

        ast::Expr::Range(_) => todo!(),

        ast::Expr::Int(_) => unify_expected_ty(
            Ty::Con(SmolStr::new_static("I32")),
            expected_ty,
            &tys.cons,
            &expr.loc,
        ),

        ast::Expr::String(parts) => {
            for part in parts {
                match part {
                    StringPart::Str(_) => continue,
                    StringPart::Expr(expr) => {
                        let expr_var = var_gen.new_var(level, expr.loc.clone());
                        preds.add(
                            Pred {
                                ty_var: expr_var.clone(),
                                trait_: Ty::to_str_view_id(),
                                assoc_tys: Default::default(),
                            },
                            &expr.loc,
                        );
                        check_expr(
                            expr,
                            Some(&Ty::Var(expr_var)),
                            return_ty,
                            level,
                            env,
                            var_gen,
                            tys,
                            preds,
                        );
                    }
                }
            }

            unify_expected_ty(
                Ty::Con(SmolStr::new_static("Str")),
                expected_ty,
                &tys.cons,
                &expr.loc,
            )
        }

        ast::Expr::Char(_) => unify_expected_ty(
            Ty::Con(SmolStr::new_static("Char")),
            expected_ty,
            &tys.cons,
            &expr.loc,
        ),

        ast::Expr::Self_ => match env.get("self") {
            Some(self_ty) => unify_expected_ty(self_ty.clone(), expected_ty, &tys.cons, &expr.loc),
            None => panic!("{}: Unbound self", loc_string(&expr.loc)),
        },

        ast::Expr::BinOp(ast::BinOpExpr { left, right, op }) => {
            let method = match op {
                ast::BinOp::Add => "__add",
                ast::BinOp::Subtract => "__sub",
                ast::BinOp::Equal => "__eq",
                ast::BinOp::NotEqual => "__neq",
                ast::BinOp::Multiply => "__mul",
                ast::BinOp::Lt => "__lt",
                ast::BinOp::Gt => "__gt",
                ast::BinOp::LtEq => "__le",
                ast::BinOp::GtEq => "__ge",
                ast::BinOp::And => "__and",
                ast::BinOp::Or => "__or",
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

            check_expr(
                &desugared,
                expected_ty,
                return_ty,
                level,
                env,
                var_gen,
                tys,
                preds,
            )
        }

        ast::Expr::UnOp(ast::UnOpExpr { op, expr }) => match op {
            ast::UnOp::Not => check_expr(
                expr,
                Some(&Ty::bool()),
                return_ty,
                level,
                env,
                var_gen,
                tys,
                preds,
            ),
        },

        ast::Expr::ArrayIndex(_) => todo!(),

        ast::Expr::Record(fields) => {
            if fields.is_empty() {
                return Ty::unit();
            }

            // TODO: For now only supporting named fields.
            let mut field_names: Set<&Id> = Default::default();
            for field in fields {
                match &field.name {
                    Some(name) => {
                        if !field_names.insert(name) {
                            panic!(
                                "{}: Field name {} occurs multiple times in the record",
                                loc_string(&expr.loc),
                                name
                            );
                        }
                    }
                    None => panic!("{}: Unnamed record field", loc_string(&expr.loc)),
                }
            }

            // To give better error messages use the field types in the expected type as expected
            // types of the expr fields when possible.
            let expected_fields =
                expected_ty.map(|expected_ty| match expected_ty.normalize(&tys.cons) {
                    Ty::Record(expected_fields) => expected_fields,
                    other => panic!(
                        "{}: Record expression expected to have type {:?}",
                        loc_string(&expr.loc),
                        other
                    ),
                });

            if let Some(expected_fields) = &expected_fields {
                let expected_field_names: Set<&Id> = expected_fields.keys().collect();
                if expected_field_names != field_names {
                    panic!(
                        "{}: Record expected to have fields {:?}, but it has fields {:?}",
                        loc_string(&expr.loc),
                        expected_field_names,
                        field_names
                    );
                }
            }

            let mut record_ty: Map<Id, Ty> = Default::default();
            for field in fields {
                let field_name = field.name.as_ref().unwrap();
                let expected_ty = expected_fields
                    .as_ref()
                    .map(|expected_fields| expected_fields.get(field_name).unwrap());
                let field_ty = check_expr(
                    &field.node,
                    expected_ty,
                    return_ty,
                    level,
                    env,
                    var_gen,
                    tys,
                    preds,
                );
                record_ty.insert(field_name.clone(), field_ty);
            }

            Ty::Record(record_ty)
        }

        ast::Expr::Return(expr) => check_expr(
            expr,
            Some(return_ty),
            return_ty,
            level,
            env,
            var_gen,
            tys,
            preds,
        ),

        ast::Expr::Match(ast::MatchExpr { scrutinee, alts }) => {
            let scrut_ty = check_expr(scrutinee, None, return_ty, level, env, var_gen, tys, preds);

            let mut rhs_tys: Vec<Ty> = Vec::with_capacity(alts.len());

            for ast::Alt {
                pattern,
                guard,
                rhs,
            } in alts
            {
                let pat_ty = check_pat(pattern, level, env, var_gen, tys, preds);
                unify(&pat_ty, &scrut_ty, &tys.cons, &pattern.loc);

                if let Some(guard) = guard {
                    check_expr(
                        guard,
                        Some(&Ty::bool()),
                        return_ty,
                        level,
                        env,
                        var_gen,
                        tys,
                        preds,
                    );
                }

                rhs_tys.push(check_stmts(
                    rhs, None, return_ty, level, env, var_gen, tys, preds,
                ));
            }

            for rhs_tys in rhs_tys.windows(2) {
                unify(&rhs_tys[0], &rhs_tys[1], &tys.cons, &expr.loc);
            }

            rhs_tys.pop().unwrap()
        }

        ast::Expr::If(ast::IfExpr {
            branches,
            else_branch,
        }) => {
            let mut branch_tys: Vec<Ty> = Vec::with_capacity(branches.len() + 1);

            for (cond, body) in branches {
                let cond_ty = check_expr(
                    cond,
                    Some(&Ty::bool()),
                    return_ty,
                    level,
                    env,
                    var_gen,
                    tys,
                    preds,
                );
                unify(&cond_ty, &Ty::bool(), &tys.cons, &expr.loc);

                let body_ty = check_stmts(
                    body,
                    expected_ty,
                    return_ty,
                    level,
                    env,
                    var_gen,
                    tys,
                    preds,
                );

                branch_tys.push(body_ty);
            }

            match else_branch {
                Some(else_body) => {
                    let body_ty = check_stmts(
                        else_body,
                        expected_ty,
                        return_ty,
                        level,
                        env,
                        var_gen,
                        tys,
                        preds,
                    );
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
                        unify(ty, expected_ty, &tys.cons, &expr.loc);
                    }
                }
                None => {
                    for ty_pair in branch_tys.windows(2) {
                        unify(&ty_pair[0], &ty_pair[1], &tys.cons, &expr.loc);
                    }
                }
            }

            branch_tys.pop().unwrap()
        }
    }
}

fn check_field_select(
    ty_con: &Id,
    ty_args: &[Ty],
    field: &Id,
    loc: &ast::Loc,
    tys: &PgmTypes,
    level: u32,
    var_gen: &mut TyVarGen,
    preds: &mut PredSet,
) -> Ty {
    match select_field(ty_con, ty_args, field, loc, tys) {
        Some(ty) => ty,
        None => match select_method(ty_con, ty_args, field, tys, loc) {
            Some(scheme) => {
                let ty = scheme.instantiate(level, var_gen, preds, loc);

                // Type arguments of the receiver already substituted for type parameters in
                // `select_method`. Drop 'self' argument.
                match ty {
                    Ty::Fun(mut args, ret) => {
                        args.remove(0);
                        Ty::Fun(args, ret)
                    }
                    _ => panic!(
                        "{}: Type of method is not a function type: {:?}",
                        loc_string(loc),
                        ty
                    ),
                }
            }
            None => panic!(
                "{}: Type {} does not have field or method {}",
                loc_string(loc),
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
    let ty_con = tys.cons.get(ty_con).unwrap();
    assert_eq!(ty_con.ty_params.len(), ty_args.len());

    match &ty_con.details {
        TyConDetails::Type(TypeDetails { cons }) => match cons.len() {
            1 => {
                let con_name = &cons[0];
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
                loc_string(loc)
            );
        }

        TyConDetails::Synonym(_) => {
            panic!("{}: Type synonym in select_field", loc_string(loc));
        }
    }
}

/// Try to select a method.
fn select_method(
    ty_con: &Id,
    ty_args: &[Ty],
    field: &Id,
    tys: &PgmTypes,
    loc: &ast::Loc,
) -> Option<Scheme> {
    let ty_con = tys.cons.get(ty_con).unwrap();
    assert_eq!(ty_con.ty_params.len(), ty_args.len());

    let ty_methods = tys.associated_schemes.get(&ty_con.id)?;
    let mut scheme = ty_methods.get(field)?.clone();

    for (ty_param, ty_arg) in ty_con.ty_params.iter().zip(ty_args.iter()) {
        scheme = scheme.subst(&ty_param.0, ty_arg, loc);
    }

    Some(scheme)
}
