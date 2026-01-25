use crate::ast::{self, Id, Named};
use crate::collections::*;
use crate::interpolation::StrPart;
use crate::mono_ast as mono;
use crate::mono_ast::MonoPgm;
use crate::type_checker::{FunArgs, Kind, RecordOrVariant, Ty};
use crate::utils::*;

use smol_str::SmolStr;

/// The program in front-end syntax, converted to a graph for efficient and easy lookups.
#[derive(Debug)]
struct PolyPgm {
    traits: HashMap<Id, PolyTrait>,

    /// Top-level functions, e.g. `foo(x: U32): ...`.
    top: HashMap<Id, ast::FunDecl>,

    /// Associated functions without `self` arguments, e.g. `Type.foo(x: U32): ...`.
    associated: HashMap<Id, HashMap<Id, ast::FunDecl>>,

    /// Associated functions with `self` arguments, e.g. `Type.bar(self, x: U32): ...`.
    method: HashMap<Id, HashMap<Id, ast::FunDecl>>,

    ty: HashMap<Id, ast::TypeDecl>,
}

/// A trait, with implementations.
#[derive(Debug, Default)]
struct PolyTrait {
    /// QVars of trait.
    ty_args: Vec<(Id, Kind)>,

    /// Implementations of the trait.
    impls: Vec<PolyTraitImpl>,
}

/// A trait implementation in the polymorpic program.
/// E.g. `impl[Iterator[iter, a]] Iterator[Map[iter, a, b], b]`.
#[derive(Debug, Default)]
struct PolyTraitImpl {
    /// Type parameters of the `impl` block, with kinds.
    ///
    /// In the example above: `[iter: *, a: *, b: *]`.
    #[allow(unused)]
    type_params: Vec<(Id, Kind)>,

    /// Type arguments of the trait.
    ///
    /// In the example above: `[Map[iter, a, b], b]`.
    tys: Vec<ast::Type>,

    methods: Vec<ast::FunDecl>,
    // We don't care about predicates, those are for type checking.
    // If a trait use type checks, then we know there will be a match in trait env during monomorph.
}

fn pgm_to_poly_pgm(pgm: Vec<ast::TopDecl>) -> PolyPgm {
    let mut traits: HashMap<Id, PolyTrait> = Default::default();
    let mut top: HashMap<Id, ast::FunDecl> = Default::default();
    let mut associated: HashMap<Id, HashMap<Id, ast::FunDecl>> = Default::default();
    let mut method: HashMap<Id, HashMap<Id, ast::FunDecl>> = Default::default();
    let mut ty: HashMap<Id, ast::TypeDecl> = Default::default();

    for decl in pgm {
        match decl {
            ast::TopDecl::Type(ty_decl) => {
                let old = ty.insert(ty_decl.node.name.clone(), ty_decl.node);
                assert!(old.is_none());
            }

            ast::TopDecl::Fun(fun_decl) => match fun_decl.node.parent_ty.clone() {
                Some(parent_ty) => match fun_decl.node.sig.self_ {
                    ast::SelfParam::No => {
                        associated
                            .entry(parent_ty.node)
                            .or_default()
                            .insert(fun_decl.node.name.node.clone(), fun_decl.node);
                    }
                    ast::SelfParam::Implicit | ast::SelfParam::Explicit(_) => {
                        method
                            .entry(parent_ty.node)
                            .or_default()
                            .insert(fun_decl.node.name.node.clone(), fun_decl.node);
                    }
                },
                None => {
                    let old = top.insert(fun_decl.node.name.node.clone(), fun_decl.node);
                    assert!(old.is_none());
                }
            },

            ast::TopDecl::Trait(trait_decl) => {
                assert_eq!(
                    trait_decl.node.type_params.len(),
                    trait_decl.node.type_param_kinds.len()
                );
                match traits.entry(trait_decl.node.name.node.clone()) {
                    Entry::Occupied(mut entry) => {
                        // We see an impl before the trait. Make sure the args were right.
                        for impl_ in &entry.get().impls {
                            assert_eq!(impl_.tys.len(), trait_decl.node.type_params.len());
                        }
                        entry.get_mut().ty_args = trait_decl
                            .node
                            .type_params
                            .iter()
                            .map(|t| t.node.clone())
                            .zip(trait_decl.node.type_param_kinds.iter().cloned())
                            .collect();
                    }
                    Entry::Vacant(entry) => {
                        entry.insert(PolyTrait {
                            ty_args: trait_decl
                                .node
                                .type_params
                                .iter()
                                .map(|t| t.node.clone())
                                .zip(trait_decl.node.type_param_kinds.iter().cloned())
                                .collect(),
                            impls: Default::default(),
                        });
                    }
                }
            }

            ast::TopDecl::Impl(impl_decl) => {
                traits
                    .entry(impl_decl.node.trait_.node.clone())
                    .or_default()
                    .impls
                    .push(PolyTraitImpl {
                        type_params: impl_decl.node.context.type_params.clone(),
                        tys: impl_decl
                            .node
                            .tys
                            .iter()
                            .map(|ty| ty.node.clone())
                            .collect(),
                        methods: impl_decl
                            .node
                            .items
                            .iter()
                            .map(|item| item.node.clone())
                            .collect(),
                    });
            }

            ast::TopDecl::Import(_) => {}
        }
    }

    PolyPgm {
        traits,
        top,
        associated,
        method,
        ty,
    }
}

pub fn monomorphise(pgm: &[ast::L<ast::TopDecl>], main: &str) -> MonoPgm {
    let poly_pgm = pgm_to_poly_pgm(pgm.iter().map(|decl| decl.node.clone()).collect());
    let mut mono_pgm = MonoPgm::default();

    // Copy types used by the interpreter built-ins.
    for ty in [
        make_ast_ty("Bool", vec![]),
        make_ast_ty("Char", vec![]),
        make_ast_ty("Str", vec![]),
        make_ast_ty("Ordering", vec![]),
        make_ast_ty("I8", vec![]),
        make_ast_ty("U8", vec![]),
        make_ast_ty("I32", vec![]),
        make_ast_ty("U32", vec![]),
        make_ast_ty("Array", vec!["I8"]),
        make_ast_ty("Array", vec!["U8"]),
        make_ast_ty("Array", vec!["I32"]),
        make_ast_ty("Array", vec!["U32"]),
        make_ast_ty("Array", vec!["I64"]),
        make_ast_ty("Array", vec!["U64"]),
    ] {
        mono_ast_ty(&ty, &Default::default(), &poly_pgm, &mut mono_pgm);
    }

    let main = poly_pgm
        .top
        .get(main)
        .unwrap_or_else(|| panic!("Main function `{main}` not defined"));

    mono_top_fn(main, &[], &poly_pgm, &mut mono_pgm);

    mono_pgm
}

fn make_ast_ty(con: &'static str, args: Vec<&'static str>) -> ast::Type {
    ast::Type::Named(ast::NamedType {
        name: SmolStr::new_static(con),
        args: args
            .into_iter()
            .map(|arg| ast::L {
                loc: ast::Loc::dummy(),
                node: (ast::Type::Named(ast::NamedType {
                    name: SmolStr::new_static(arg),
                    args: vec![],
                })),
            })
            .collect(),
    })
}

fn mono_top_fn(
    fun_decl: &ast::FunDecl,
    ty_args: &[mono::Type],
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) {
    assert_eq!(fun_decl.sig.context.type_params.len(), ty_args.len());

    let ty_map: HashMap<Id, mono::Type> = fun_decl
        .sig
        .context
        .type_params
        .iter()
        .map(|(ty_param, _)| ty_param.clone())
        .zip(ty_args.iter().cloned())
        .collect();

    let mut params: Vec<(Id, ast::L<mono::Type>)> =
        Vec::with_capacity(fun_decl.sig.params.len() + 1);

    match &fun_decl.sig.self_ {
        ast::SelfParam::No => {}
        ast::SelfParam::Implicit => {
            // Same as the type checker: function should be an associated function, and the parent
            // type should not have type parameters.
            // TODO: Type checker should annotate all self types instead.
            let self_ty_con = fun_decl.parent_ty.as_ref().unwrap().node.clone();
            assert!(
                poly_pgm
                    .ty
                    .get(&self_ty_con)
                    .unwrap()
                    .type_params
                    .is_empty()
            );
            params.push((
                SmolStr::new_static("self"),
                ast::L::new_dummy(mono::Type::Named(mono::NamedType {
                    name: self_ty_con,
                    args: vec![],
                })),
            ));
        }
        ast::SelfParam::Explicit(self_ty) => {
            let self_mono_ty = mono_l_ty(self_ty, &ty_map, poly_pgm, mono_pgm);
            params.push((SmolStr::new_static("self"), self_mono_ty));
        }
    }

    params.extend(fun_decl.sig.params.iter().map(|(param_name, param_ty)| {
        (
            param_name.clone(),
            mono_l_ty(param_ty.as_ref().unwrap(), &ty_map, poly_pgm, mono_pgm),
        )
    }));

    let return_ty: Option<ast::L<mono::Type>> =
        mono_opt_l_ty(&fun_decl.sig.return_ty, &ty_map, poly_pgm, mono_pgm);

    let exceptions: Option<ast::L<mono::Type>> =
        mono_opt_l_ty(&fun_decl.sig.exceptions, &ty_map, poly_pgm, mono_pgm);

    // Check if we've already monomorphised this function.
    // Add current function to mono_pgm without a body to avoid looping.
    match &fun_decl.parent_ty {
        Some(parent_ty) => {
            match mono_pgm
                .associated
                .entry(parent_ty.node.clone())
                .or_default()
                .entry(fun_decl.name.node.clone())
                .or_default()
                .entry(ty_args.to_vec())
            {
                Entry::Occupied(_) => return,
                Entry::Vacant(entry) => {
                    entry.insert(mono::FunDecl {
                        parent_ty: fun_decl.parent_ty.clone(),
                        name: fun_decl.name.clone(),
                        sig: mono::FunSig {
                            params,
                            return_ty,
                            exceptions,
                        },
                        body: None,
                    });
                }
            }
        }
        None => {
            match mono_pgm
                .funs
                .entry(fun_decl.name.node.clone())
                .or_default()
                .entry(ty_args.to_vec())
            {
                Entry::Occupied(_) => return,
                Entry::Vacant(entry) => {
                    entry.insert(mono::FunDecl {
                        parent_ty: None,
                        name: fun_decl.name.clone(),
                        sig: mono::FunSig {
                            params,
                            return_ty,
                            exceptions,
                        },
                        body: None,
                    });
                }
            }
        }
    }

    // Monomorphise function body.
    let body = match &fun_decl.body {
        Some(body) => body,
        None => return,
    };

    let mut locals: ScopeSet<Id> = Default::default();
    fun_decl
        .sig
        .params
        .iter()
        .for_each(|(id, _)| locals.insert(id.clone()));

    let mono_body = mono_l_stmts(body, &ty_map, poly_pgm, mono_pgm, &mut locals);

    match &fun_decl.parent_ty {
        Some(parent_ty) => {
            mono_pgm
                .associated
                .get_mut(&parent_ty.node)
                .unwrap()
                .get_mut(&fun_decl.name.node)
                .unwrap()
                .get_mut(ty_args)
                .unwrap()
                .body = Some(mono_body);
        }
        None => {
            mono_pgm
                .funs
                .get_mut(&fun_decl.name.node)
                .unwrap()
                .get_mut(ty_args)
                .unwrap()
                .body = Some(mono_body);
        }
    }
}

fn mono_stmt(
    stmt: &ast::Stmt,
    ty_map: &HashMap<Id, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    locals: &mut ScopeSet<Id>,
    loc: &ast::Loc,
) -> mono::Stmt {
    match stmt {
        ast::Stmt::Break { label, level } => mono::Stmt::Break {
            label: label.clone(),
            level: *level,
        },

        ast::Stmt::Continue { label, level } => mono::Stmt::Continue {
            label: label.clone(),
            level: *level,
        },

        ast::Stmt::Let(ast::LetStmt { lhs, ty: _, rhs }) => {
            let rhs = mono_l_expr(rhs, ty_map, poly_pgm, mono_pgm, locals);
            let lhs = mono_l_pat(lhs, ty_map, poly_pgm, mono_pgm, locals);
            mono::Stmt::Let(mono::LetStmt { lhs, rhs })
        }

        ast::Stmt::Assign(ast::AssignStmt { lhs, rhs, op }) => {
            // Complex assignment operators should've been desugared during type checking.
            assert_eq!(
                *op,
                ast::AssignOp::Eq,
                "{}: Complex assignment: {:?}",
                loc_display(loc),
                op
            );
            mono::Stmt::Assign(mono::AssignStmt {
                lhs: mono_l_expr(lhs, ty_map, poly_pgm, mono_pgm, locals),
                rhs: mono_l_expr(rhs, ty_map, poly_pgm, mono_pgm, locals),
            })
        }

        ast::Stmt::Expr(expr) => {
            mono::Stmt::Expr(mono_expr(expr, ty_map, poly_pgm, mono_pgm, locals, loc))
        }

        ast::Stmt::For(ast::ForStmt { .. }) => {
            panic!("{}: For loop should've been desugared", loc_display(loc))
        }

        ast::Stmt::While(ast::WhileStmt { label, cond, body }) => {
            let cond = mono_l_expr(cond, ty_map, poly_pgm, mono_pgm, locals);
            locals.enter();
            let body = mono_l_stmts(body, ty_map, poly_pgm, mono_pgm, locals);
            locals.exit();
            mono::Stmt::While(mono::WhileStmt {
                label: label.clone(),
                cond,
                body,
            })
        }
    }
}

// ty_map: maps type variables in scope to their mono types.
fn mono_expr(
    expr: &ast::Expr,
    ty_map: &HashMap<Id, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    locals: &mut ScopeSet<Id>,
    loc: &ast::Loc,
) -> mono::Expr {
    match expr {
        ast::Expr::Var(ast::VarExpr {
            id: var,
            user_ty_args: _,
            ty_args,
        }) => {
            if locals.is_bound(var) {
                // Local variable, cannot be polymorphic.
                assert!(ty_args.is_empty());
                return mono::Expr::LocalVar(var.clone());
            }

            let poly_decl = poly_pgm
                .top
                .get(var)
                .unwrap_or_else(|| panic!("{}: Unbound variable {}", loc_display(loc), var));

            let mono_ty_args = ty_args
                .iter()
                .map(|ty| mono_tc_ty(ty, ty_map, poly_pgm, mono_pgm))
                .collect::<Vec<_>>();

            mono_top_fn(poly_decl, &mono_ty_args, poly_pgm, mono_pgm);

            mono::Expr::TopVar(mono::VarExpr {
                id: var.clone(),
                ty_args: mono_ty_args,
            })
        }

        ast::Expr::FieldSel(ast::FieldSelExpr {
            object,
            field,
            user_ty_args: _,
        }) => mono::Expr::FieldSel(mono::FieldSelExpr {
            object: mono_bl_expr(object, ty_map, poly_pgm, mono_pgm, locals),
            field: field.clone(),
        }),

        ast::Expr::MethodSel(ast::MethodSelExpr {
            object,       // receiver
            object_ty,    // receiver type
            method_ty_id, // type that the method belongs to: `trait` or `type`
            method,       // method or associated function name
            ty_args,      // function type arguments
        }) => {
            let mono_ty_args: Vec<mono::Type> = ty_args
                .iter()
                .map(|ty| mono_tc_ty(ty, ty_map, poly_pgm, mono_pgm))
                .collect();

            mono_method(method_ty_id, method, &mono_ty_args, poly_pgm, mono_pgm, loc);

            let mono_object = mono_bl_expr(object, ty_map, poly_pgm, mono_pgm, locals);

            let mono_object_ty =
                mono_tc_ty(object_ty.as_ref().unwrap(), ty_map, poly_pgm, mono_pgm);

            /*
            <receiver>.<method>

            ==>

            do:
                let receiver = <receiver>
                \(...args): <receiver_type>.<method>(reciver, ...args)
            */

            let mono_fun = mono_pgm
                .associated
                .get(method_ty_id)
                .unwrap()
                .get(method)
                .unwrap()
                .get(&mono_ty_args)
                .unwrap();

            let mono::FnType { args, ret, exn } = mono_fun.sig.ty();

            let mono_fun_args = match args {
                mono::FunArgs::Positional(args) => args,
                mono::FunArgs::Named(_) => {
                    // Methods can't have named arguments.
                    panic!()
                }
            };

            let closure_params: Vec<(Id, mono::L<mono::Type>)> = mono_fun_args
                .iter()
                .skip(1) // skip receiver
                .enumerate()
                .map(|(i, arg_ty)| {
                    (
                        SmolStr::new(format!("$arg{}$", i)),
                        mono::L {
                            loc: loc.clone(),
                            node: arg_ty.clone(),
                        },
                    )
                })
                .collect();

            let receiver_id = SmolStr::new_static("$receiver$");

            let assoc_fn_args: Vec<mono::CallArg> = std::iter::once(receiver_id.clone())
                .chain(closure_params.iter().map(|(arg, _)| arg.clone()))
                .map(|arg| mono::CallArg {
                    name: None,
                    expr: ast::L {
                        loc: loc.clone(),
                        node: mono::Expr::LocalVar(arg.clone()),
                    },
                })
                .collect();

            mono::Expr::Do(vec![
                mono::L {
                    loc: loc.clone(),
                    node: mono::Stmt::Let(mono::LetStmt {
                        lhs: mono::L {
                            loc: loc.clone(),
                            node: mono::Pat::Var(mono::VarPat {
                                var: SmolStr::new_static("$receiver$"),
                                ty: mono_object_ty,
                            }),
                        },
                        rhs: *mono_object,
                    }),
                },
                mono::L {
                    loc: loc.clone(),
                    node: mono::Stmt::Expr(mono::Expr::Fn(mono::FnExpr {
                        sig: mono::FunSig {
                            params: closure_params,
                            return_ty: Some(ast::L::new_dummy((*ret).clone())),
                            exceptions: Some(ast::L::new_dummy((*exn).clone())),
                        },
                        body: vec![mono::L {
                            loc: loc.clone(),
                            node: mono::Stmt::Expr(mono::Expr::Call(mono::CallExpr {
                                fun: Box::new(ast::L {
                                    loc: loc.clone(),
                                    node: mono::Expr::AssocFnSel(mono::AssocFnSelExpr {
                                        ty: method_ty_id.clone(),
                                        member: method.clone(),
                                        ty_args: mono_ty_args,
                                    }),
                                }),
                                args: assoc_fn_args,
                            })),
                        }],
                    })),
                },
            ])
        }

        ast::Expr::ConSel(ast::Con {
            ty,
            con,
            user_ty_args: _,
            ty_args,
        }) => match con {
            Some(con) => {
                let poly_ty_decl = poly_pgm.ty.get(ty).unwrap();

                let mono_ty_args = ty_args
                    .iter()
                    .map(|ty| mono_tc_ty(ty, ty_map, poly_pgm, mono_pgm))
                    .collect::<Vec<_>>();

                let mono_ty_id = mono_ty_decl(poly_ty_decl, &mono_ty_args, poly_pgm, mono_pgm);
                mono::Expr::ConSel(mono::Con {
                    ty: mono_ty_id,
                    con: Some(con.clone()),
                    ty_args: mono_ty_args,
                })
            }
            None => {
                let poly_ty_decl = match poly_pgm.ty.get(ty) {
                    None => panic!("Unknown constructor {ty}"),
                    Some(ty_decl) => ty_decl,
                };

                let mono_ty_args = ty_args
                    .iter()
                    .map(|ty| mono_tc_ty(ty, ty_map, poly_pgm, mono_pgm))
                    .collect::<Vec<_>>();

                let mono_ty_id = mono_ty_decl(poly_ty_decl, &mono_ty_args, poly_pgm, mono_pgm);

                mono::Expr::ConSel(mono::Con {
                    ty: mono_ty_id,
                    con: None,
                    ty_args: mono_ty_args,
                })
            }
        },

        ast::Expr::AssocFnSel(ast::AssocFnSelExpr {
            ty,
            ty_user_ty_args: _,
            member,
            user_ty_args: _,
            ty_args,
        }) => {
            let mono_ty_args: Vec<mono::Type> = ty_args
                .iter()
                .map(|ty_arg| mono_tc_ty(ty_arg, ty_map, poly_pgm, mono_pgm))
                .collect();

            // Check associated functions.
            if let Some(fun_decl) = poly_pgm
                .associated
                .get(ty)
                .and_then(|ty_map| ty_map.get(member))
                .or_else(|| {
                    poly_pgm
                        .method
                        .get(ty)
                        .and_then(|ty_map| ty_map.get(member))
                })
            {
                mono_top_fn(fun_decl, &mono_ty_args, poly_pgm, mono_pgm);

                return mono::Expr::AssocFnSel(mono::AssocFnSelExpr {
                    ty: ty.clone(),
                    member: member.clone(),
                    ty_args: mono_ty_args,
                });
            }

            // Check traits.
            if poly_pgm.traits.contains_key(ty) {
                mono_method(ty, member, &mono_ty_args, poly_pgm, mono_pgm, loc);
                return mono::Expr::AssocFnSel(mono::AssocFnSelExpr {
                    ty: ty.clone(),
                    member: member.clone(),
                    ty_args: mono_ty_args,
                });
            }

            panic!(
                "{}: Associated function or method {}.{} isn't in poly pgm",
                loc_display(loc),
                ty,
                member
            )
        }

        ast::Expr::Int(int @ ast::IntExpr { kind, .. }) => {
            let ty_decl_id = match kind.unwrap() {
                ast::IntKind::I8(_) => "I8",
                ast::IntKind::U8(_) => "U8",
                ast::IntKind::I32(_) => "I32",
                ast::IntKind::U32(_) => "U32",
                ast::IntKind::I64(_) => "I64",
                ast::IntKind::U64(_) => "U64",
            };
            let ty_decl = poly_pgm.ty.get(ty_decl_id).unwrap();
            mono_ty_decl(ty_decl, &[], poly_pgm, mono_pgm);
            mono::Expr::Int(int.clone())
        }

        ast::Expr::Char(char) => {
            let ty_decl = poly_pgm.ty.get("Char").unwrap();
            mono_ty_decl(ty_decl, &[], poly_pgm, mono_pgm);
            mono::Expr::Char(*char)
        }

        ast::Expr::Self_ => mono::Expr::LocalVar(SmolStr::new_static("self")),

        ast::Expr::Call(ast::CallExpr { fun, args }) => mono::Expr::Call(mono::CallExpr {
            fun: mono_bl_expr(fun, ty_map, poly_pgm, mono_pgm, locals),
            args: args
                .iter()
                .map(|ast::CallArg { name, expr }| mono::CallArg {
                    name: name.clone(),
                    expr: mono_l_expr(expr, ty_map, poly_pgm, mono_pgm, locals),
                })
                .collect(),
        }),

        ast::Expr::Str(parts) => {
            if parts.len() != 1 {
                panic!("{}: Non-desugared string literal", loc_display(loc));
            }
            let str = match &parts[0] {
                StrPart::Expr(_) => {
                    panic!("{}: Non-desugared string literal", loc_display(loc));
                }
                StrPart::Str(str) => str,
            };
            mono::Expr::Str(str.clone())
        }

        ast::Expr::BinOp(ast::BinOpExpr { left, right, op }) => {
            mono::Expr::BinOp(mono::BinOpExpr {
                left: mono_bl_expr(left, ty_map, poly_pgm, mono_pgm, locals),
                right: mono_bl_expr(right, ty_map, poly_pgm, mono_pgm, locals),
                op: *op,
            })
        }

        ast::Expr::UnOp(ast::UnOpExpr { op, expr: _ }) => match op {
            ast::UnOp::Neg => panic!("Neg unop wasn't desugred"),
            ast::UnOp::Not => panic!("Not unop wasn't desugared"),
        },

        ast::Expr::Return(expr) => {
            mono::Expr::Return(mono_bl_expr(expr, ty_map, poly_pgm, mono_pgm, locals))
        }

        ast::Expr::Match(ast::MatchExpr { scrutinee, alts }) => {
            mono::Expr::Match(mono::MatchExpr {
                scrutinee: mono_bl_expr(scrutinee, ty_map, poly_pgm, mono_pgm, locals),
                alts: alts
                    .iter()
                    .map(|ast::Alt { pat, guard, rhs }| {
                        locals.enter();
                        let alt = mono::Alt {
                            pat: mono_l_pat(pat, ty_map, poly_pgm, mono_pgm, locals),
                            guard: guard
                                .as_ref()
                                .map(|expr| mono_l_expr(expr, ty_map, poly_pgm, mono_pgm, locals)),
                            rhs: mono_l_stmts(rhs, ty_map, poly_pgm, mono_pgm, locals),
                        };
                        locals.exit();
                        alt
                    })
                    .collect(),
            })
        }

        ast::Expr::If(ast::IfExpr {
            branches,
            else_branch,
            inferred_ty: _,
        }) => mono::Expr::If(mono::IfExpr {
            branches: branches
                .iter()
                .map(|(expr, stmts)| {
                    let cond = mono_l_expr(expr, ty_map, poly_pgm, mono_pgm, locals);
                    locals.enter();
                    let stmts = mono_l_stmts(stmts, ty_map, poly_pgm, mono_pgm, locals);
                    locals.exit();
                    (cond, stmts)
                })
                .collect(),
            else_branch: else_branch.as_ref().map(|stmts| {
                locals.enter();
                let stmts = mono_l_stmts(stmts, ty_map, poly_pgm, mono_pgm, locals);
                locals.exit();
                stmts
            }),
        }),

        ast::Expr::Fn(ast::FnExpr {
            sig,
            body,
            inferred_ty,
        }) => {
            let (args, ret, exceptions) = match inferred_ty.as_ref().unwrap() {
                Ty::Fun {
                    args,
                    ret,
                    exceptions,
                } => (
                    match args {
                        FunArgs::Positional(args) => args,
                        FunArgs::Named(_) => panic!(),
                    },
                    ret,
                    exceptions,
                ),
                _ => panic!(),
            };

            assert_eq!(args.len(), sig.params.len());

            locals.enter();
            sig.params
                .iter()
                .for_each(|(arg, _)| locals.insert(arg.clone()));
            let body = mono_l_stmts(body, ty_map, poly_pgm, mono_pgm, locals);
            locals.exit();

            mono::Expr::Fn(mono::FnExpr {
                sig: mono::FunSig {
                    params: sig
                        .params
                        .iter()
                        .zip(args.iter())
                        .map(|((arg, _ast_ty), ty)| {
                            (
                                arg.clone(),
                                ast::L {
                                    loc: loc.clone(),
                                    node: mono_tc_ty(ty, ty_map, poly_pgm, mono_pgm),
                                },
                            )
                        })
                        .collect(),
                    return_ty: Some(ast::L {
                        loc: loc.clone(),
                        node: mono_tc_ty(ret, ty_map, poly_pgm, mono_pgm),
                    }),
                    exceptions: exceptions.as_ref().map(|ty| ast::L {
                        loc: loc.clone(),
                        node: mono_tc_ty(ty, ty_map, poly_pgm, mono_pgm),
                    }),
                },
                body,
            })
        }

        ast::Expr::Is(ast::IsExpr { expr, pat }) => mono::Expr::Is(mono::IsExpr {
            expr: mono_bl_expr(expr, ty_map, poly_pgm, mono_pgm, locals),
            pat: mono_l_pat(pat, ty_map, poly_pgm, mono_pgm, locals),
        }),

        ast::Expr::Do(ast::DoExpr {
            stmts,
            inferred_ty: _,
        }) => mono::Expr::Do(mono_l_stmts(stmts, ty_map, poly_pgm, mono_pgm, locals)),

        ast::Expr::Seq { .. } => panic!("Seq expr should've been desugared"),

        ast::Expr::Record(ast::RecordExpr {
            fields,
            inferred_ty,
        }) => mono::Expr::Record(mono::RecordExpr {
            fields: fields
                .iter()
                .map(|(field_name, field_expr)| {
                    (
                        field_name.clone(),
                        mono_l_expr(field_expr, ty_map, poly_pgm, mono_pgm, locals),
                    )
                })
                .collect(),

            ty: get_record_ty(
                mono_tc_ty(inferred_ty.as_ref().unwrap(), ty_map, poly_pgm, mono_pgm),
                loc,
            ),
        }),

        ast::Expr::Variant(ast::VariantExpr { expr, inferred_ty }) => {
            mono::Expr::Variant(mono::VariantExpr {
                expr: mono_bl_expr(expr, ty_map, poly_pgm, mono_pgm, locals),
                ty: get_variant_ty(
                    mono_tc_ty(inferred_ty.as_ref().unwrap(), ty_map, poly_pgm, mono_pgm),
                    loc,
                ),
            })
        }
    }
}

// Monomorphise a trait or non-trait method.
//
// Example for traits: `x.next` where `x: Map[Chars, Char, U32]`.
//
// - method_ty_id: `Iterator`
// - method_id: `next`
// - ty_args: `[Map[Chars, Char, U32], U32, exn]`
//     (type arguments to `Iterator.next`)
//     (`exn` is the exception type)
//
// Example for non-traits: `x.push` where `x: Vec[U32]`.
//
// - method_ty_id: `Vec`
// - method_id: `push`
// - ty_args: `[U32, exn]`
fn mono_method(
    method_ty_id: &Id,      // type that the method belonds to: `trait` or `type`
    method_id: &Id,         // method name
    ty_args: &[mono::Type], // method type arguments, including the trait or type's
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    loc: &ast::Loc,
) {
    if let Some(PolyTrait {
        ty_args: trait_ty_args,
        impls,
    }) = poly_pgm.traits.get(method_ty_id)
    {
        // Find the matching impl.
        for impl_ in impls {
            if let Some(mut substs) = match_trait_impl(&ty_args[0..trait_ty_args.len()], impl_) {
                let method: &ast::FunDecl = impl_
                    .methods
                    .iter()
                    .find(|fun_decl| &fun_decl.name.node == method_id)
                    .unwrap();

                // Bind function type parameters.
                for ((ty_param, _kind), ty_arg) in method
                    .sig
                    .context
                    .type_params
                    .iter()
                    .zip(&ty_args[trait_ty_args.len()..])
                {
                    substs.insert(ty_param.clone(), ty_arg.clone());
                }

                let mut params: Vec<(Id, ast::L<mono::Type>)> =
                    Vec::with_capacity(method.sig.params.len() + 1);

                match &method.sig.self_ {
                    ast::SelfParam::No => {}
                    ast::SelfParam::Implicit => panic!(),
                    ast::SelfParam::Explicit(self_ty) => {
                        let self_mono_ty = mono_l_ty(self_ty, &substs, poly_pgm, mono_pgm);
                        params.push((SmolStr::new_static("self"), self_mono_ty));
                    }
                }

                params.extend(method.sig.params.iter().map(|(param_name, param_ty)| {
                    (
                        param_name.clone(),
                        mono_l_ty(param_ty.as_ref().unwrap(), &substs, poly_pgm, mono_pgm),
                    )
                }));

                let return_ty: Option<ast::L<mono::Type>> =
                    mono_opt_l_ty(&method.sig.return_ty, &substs, poly_pgm, mono_pgm);

                let exceptions: Option<ast::L<mono::Type>> =
                    mono_opt_l_ty(&method.sig.exceptions, &substs, poly_pgm, mono_pgm);

                // See if we already monomorphised this method.
                match mono_pgm
                    .associated
                    .entry(method_ty_id.clone())
                    .or_default()
                    .entry(method_id.clone())
                    .or_default()
                    .entry(ty_args.to_vec())
                {
                    Entry::Occupied(_) => {
                        return;
                    }
                    Entry::Vacant(entry) => {
                        entry.insert(mono::FunDecl {
                            parent_ty: Some(ast::L {
                                node: method_ty_id.clone(),
                                loc: ast::Loc::dummy(),
                            }),
                            name: method.name.set_node(method_id.clone()),
                            sig: mono::FunSig {
                                params,
                                return_ty,
                                exceptions,
                            },
                            body: None,
                        });
                    }
                }

                // Monomorphise method body.
                let body = match &method.body {
                    Some(body) => body,
                    None => return,
                };

                let mut locals: ScopeSet<Id> = Default::default();
                method
                    .sig
                    .params
                    .iter()
                    .for_each(|(id, _)| locals.insert(id.clone()));

                let mono_body = mono_l_stmts(body, &substs, poly_pgm, mono_pgm, &mut locals);

                mono_pgm
                    .associated
                    .get_mut(method_ty_id)
                    .unwrap()
                    .get_mut(method_id)
                    .unwrap()
                    .get_mut(ty_args)
                    .unwrap()
                    .body = Some(mono_body);

                return;
            }
        }

        let args = ty_args
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<String>>()
            .join(", ");

        panic!(
            "{}: Unable to find matching impl for {} type args [{}]",
            loc_display(loc),
            method_ty_id,
            args,
        );
    }

    if let Some(method_map) = poly_pgm.method.get(method_ty_id) {
        let method: &ast::FunDecl = method_map.get(method_id).unwrap();

        let ty_map: HashMap<Id, mono::Type> = method
            .sig
            .context
            .type_params
            .iter()
            .map(|(ty_param, _)| ty_param.clone())
            .zip(ty_args.iter().cloned())
            .collect();

        let mut params: Vec<(Id, ast::L<mono::Type>)> =
            Vec::with_capacity(method.sig.params.len() + 1);

        match &method.sig.self_ {
            ast::SelfParam::No => {}
            ast::SelfParam::Implicit => {
                // Same as the type checker: function should be an associated function, and the parent
                // type should not have type parameters.
                // TODO: Type checker should annotate all self types instead.
                let self_ty_con = method.parent_ty.as_ref().unwrap().node.clone();
                assert!(
                    poly_pgm
                        .ty
                        .get(&self_ty_con)
                        .unwrap()
                        .type_params
                        .is_empty()
                );
                params.push((
                    SmolStr::new_static("self"),
                    ast::L::new_dummy(mono::Type::Named(mono::NamedType {
                        name: self_ty_con,
                        args: vec![],
                    })),
                ));
            }
            ast::SelfParam::Explicit(self_ty) => {
                let self_mono_ty = mono_l_ty(self_ty, &ty_map, poly_pgm, mono_pgm);
                params.push((SmolStr::new_static("self"), self_mono_ty));
            }
        }

        params.extend(method.sig.params.iter().map(|(param_name, param_ty)| {
            (
                param_name.clone(),
                mono_l_ty(param_ty.as_ref().unwrap(), &ty_map, poly_pgm, mono_pgm),
            )
        }));

        let return_ty: Option<ast::L<mono::Type>> =
            mono_opt_l_ty(&method.sig.return_ty, &ty_map, poly_pgm, mono_pgm);

        let exceptions: Option<ast::L<mono::Type>> =
            mono_opt_l_ty(&method.sig.exceptions, &ty_map, poly_pgm, mono_pgm);

        // See if we already monomorphised this method.
        match mono_pgm
            .associated
            .entry(method_ty_id.clone())
            .or_default()
            .entry(method_id.clone())
            .or_default()
            .entry(ty_args.to_vec())
        {
            Entry::Occupied(_) => {
                return;
            }
            Entry::Vacant(entry) => {
                entry.insert(mono::FunDecl {
                    parent_ty: Some(ast::L {
                        node: method_ty_id.clone(),
                        loc: ast::Loc::dummy(),
                    }),
                    name: method.name.set_node(method_id.clone()),
                    sig: mono::FunSig {
                        params,
                        return_ty,
                        exceptions,
                    },
                    body: None,
                });
            }
        }

        // Monomorphise method body.
        let body = match &method.body {
            Some(body) => body,
            None => return,
        };

        let mut locals: ScopeSet<Id> = Default::default();
        method
            .sig
            .params
            .iter()
            .for_each(|(id, _)| locals.insert(id.clone()));

        let mono_body = mono_l_stmts(body, &ty_map, poly_pgm, mono_pgm, &mut locals);

        mono_pgm
            .associated
            .get_mut(method_ty_id)
            .unwrap()
            .get_mut(method_id)
            .unwrap()
            .get_mut(ty_args)
            .unwrap()
            .body = Some(mono_body);

        return;
    }

    panic!("Type {method_ty_id} is not a trait or type")
}

fn mono_l_stmts(
    lstmts: &[ast::L<ast::Stmt>],
    ty_map: &HashMap<Id, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    locals: &mut ScopeSet<Id>,
) -> Vec<ast::L<mono::Stmt>> {
    lstmts
        .iter()
        .map(|lstmt| {
            lstmt.map_as_ref(|stmt| mono_stmt(stmt, ty_map, poly_pgm, mono_pgm, locals, &lstmt.loc))
        })
        .collect()
}

fn mono_bl_expr(
    expr: &ast::L<ast::Expr>,
    ty_map: &HashMap<Id, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    locals: &mut ScopeSet<Id>,
) -> Box<ast::L<mono::Expr>> {
    Box::new(
        expr.map_as_ref(|expr_| mono_expr(expr_, ty_map, poly_pgm, mono_pgm, locals, &expr.loc)),
    )
}

fn mono_l_expr(
    expr: &ast::L<ast::Expr>,
    ty_map: &HashMap<Id, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    locals: &mut ScopeSet<Id>,
) -> ast::L<mono::Expr> {
    expr.map_as_ref(|expr_| mono_expr(expr_, ty_map, poly_pgm, mono_pgm, locals, &expr.loc))
}

fn mono_pat(
    pat: &ast::Pat,
    ty_map: &HashMap<Id, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    locals: &mut ScopeSet<Id>,
    loc: &ast::Loc,
) -> mono::Pat {
    match pat {
        ast::Pat::Var(ast::VarPat { var, ty }) => {
            let mono_ty = mono_tc_ty(ty.as_ref().unwrap(), ty_map, poly_pgm, mono_pgm);
            locals.insert(var.clone());
            mono::Pat::Var(mono::VarPat {
                var: var.clone(),
                ty: mono_ty,
            })
        }

        ast::Pat::Ignore => mono::Pat::Ignore,

        ast::Pat::Str(str) => mono::Pat::Str(str.clone()),

        ast::Pat::Char(c) => mono::Pat::Char(*c),

        ast::Pat::Or(pat1, pat2) => mono::Pat::Or(
            mono_bl_pat(pat1, ty_map, poly_pgm, mono_pgm, locals),
            mono_bl_pat(pat2, ty_map, poly_pgm, mono_pgm, locals),
        ),

        ast::Pat::Con(ast::ConPat {
            con:
                ast::Con {
                    ty,
                    con,
                    user_ty_args: _,
                    ty_args,
                },
            fields,
            ignore_rest: _,
        }) => {
            let ty_decl = poly_pgm.ty.get(ty).unwrap();

            let mono_ty_args: Vec<mono::Type> = ty_args
                .iter()
                .map(|ty_arg| mono_tc_ty(ty_arg, ty_map, poly_pgm, mono_pgm))
                .collect();

            let mono_ty_id = mono_ty_decl(
                ty_decl,
                &mono_ty_args[0..ty_decl.type_params.len()],
                poly_pgm,
                mono_pgm,
            );

            let mono_fields: Vec<Named<ast::L<mono::Pat>>> = fields
                .iter()
                .map(|field| mono_named_l_pat(field, ty_map, poly_pgm, mono_pgm, locals))
                .collect();

            mono::Pat::Con(mono::ConPat {
                con: mono::Con {
                    ty: mono_ty_id,
                    con: con.clone(),
                    ty_args: mono_ty_args,
                },
                fields: mono_fields,
            })
        }

        ast::Pat::Record(ast::RecordPat {
            fields,
            ignore_rest: _,
            inferred_ty,
        }) => mono::Pat::Record(mono::RecordPat {
            fields: fields
                .iter()
                .map(|named_pat| mono_named_l_pat(named_pat, ty_map, poly_pgm, mono_pgm, locals))
                .collect(),
            ty: get_record_ty(
                mono_tc_ty(inferred_ty.as_ref().unwrap(), ty_map, poly_pgm, mono_pgm),
                loc,
            ),
        }),

        ast::Pat::Variant(ast::VariantPat { pat, inferred_ty }) => {
            mono::Pat::Variant(mono::VariantPat {
                pat: mono_bl_pat(pat, ty_map, poly_pgm, mono_pgm, locals),
                ty: get_variant_ty(
                    mono_tc_ty(inferred_ty.as_ref().unwrap(), ty_map, poly_pgm, mono_pgm),
                    loc,
                ),
            })
        }
    }
}

fn mono_l_pat(
    pat: &ast::L<ast::Pat>,
    ty_map: &HashMap<Id, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    locals: &mut ScopeSet<Id>,
) -> ast::L<mono::Pat> {
    pat.map_as_ref(|pat_| mono_pat(pat_, ty_map, poly_pgm, mono_pgm, locals, &pat.loc))
}

fn mono_bl_pat(
    pat: &ast::L<ast::Pat>,
    ty_map: &HashMap<Id, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    locals: &mut ScopeSet<Id>,
) -> Box<ast::L<mono::Pat>> {
    Box::new(mono_l_pat(pat, ty_map, poly_pgm, mono_pgm, locals))
}

fn mono_named_l_pat(
    pat: &Named<ast::L<ast::Pat>>,
    ty_map: &HashMap<Id, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    locals: &mut ScopeSet<Id>,
) -> Named<ast::L<mono::Pat>> {
    pat.map_as_ref(|pat| mono_l_pat(pat, ty_map, poly_pgm, mono_pgm, locals))
}

fn mono_l_ty(
    ty: &ast::L<ast::Type>,
    ty_map: &HashMap<Id, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> ast::L<mono::Type> {
    ty.map_as_ref(|ty| mono_ast_ty(ty, ty_map, poly_pgm, mono_pgm))
}

fn mono_opt_l_ty(
    ty: &Option<ast::L<ast::Type>>,
    ty_map: &HashMap<Id, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> Option<ast::L<mono::Type>> {
    ty.as_ref()
        .map(|ty| mono_l_ty(ty, ty_map, poly_pgm, mono_pgm))
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Trait matching

fn match_trait_impl(
    ty_args: &[mono::Type],
    trait_impl: &PolyTraitImpl,
) -> Option<HashMap<Id, mono::Type>> {
    debug_assert_eq!(ty_args.len(), trait_impl.tys.len(), "{ty_args:?}");

    let mut substs: HashMap<Id, mono::Type> = Default::default();
    for (impl_ty_arg, ty_arg) in trait_impl.tys.iter().zip(ty_args.iter()) {
        if !match_(impl_ty_arg, ty_arg, &mut substs) {
            return None;
        }
    }

    Some(substs)
}

fn match_(
    impl_ty_arg: &ast::Type,
    arg_ty: &mono::Type,
    substs: &mut HashMap<Id, mono::Type>,
) -> bool {
    match (impl_ty_arg, arg_ty) {
        (ast::Type::Named(trait_named_ty), mono::Type::Named(arg_named_ty)) => {
            match_named_ty(trait_named_ty, arg_named_ty, substs)
        }

        (
            ast::Type::Record {
                fields: fields1,
                extension,
                is_row: _, // TODO: Do we need to check this?
            },
            mono::Type::Record { fields: fields2 },
        ) => {
            let fields1_map: HashMap<&Id, &ast::Type> = fields1
                .iter()
                .map(|(field_name, field_ty)| (field_name, field_ty))
                .collect();

            let mut fields2_map: HashMap<&Id, &mono::Type> = fields2.iter().collect();

            for (field_name, field1_ty) in &fields1_map {
                let field2_ty = match fields2_map.remove(field_name) {
                    Some(field2_ty) => field2_ty,
                    None => return false,
                };
                if !match_(field1_ty, field2_ty, substs) {
                    return false;
                }
            }

            if !fields2_map.is_empty() && extension.is_none() {
                return false;
            }

            if !fields2_map.is_empty() {
                substs.insert(
                    extension.as_ref().unwrap().clone(),
                    mono::Type::Record {
                        fields: fields2_map
                            .iter()
                            .map(|(field2_name, field2_ty)| {
                                ((*field2_name).clone(), (*field2_ty).clone())
                            })
                            .collect(),
                    },
                );
            }

            true
        }

        (
            ast::Type::Variant {
                alts: alts1,
                extension,
                is_row: _,
            },
            mono::Type::Variant { alts: alts2 },
        ) => {
            let mut labels1_map: HashMap<Id, ast::NamedType> = Default::default();
            for alt1_ty in alts1 {
                let old = labels1_map.insert(alt1_ty.name.clone(), alt1_ty.clone());
                assert!(old.is_none());
            }

            let mut labels2_map: OrdMap<Id, mono::NamedType> = Default::default();
            for alt2_ty in alts2.values() {
                let old = labels2_map.insert(alt2_ty.name.clone(), alt2_ty.clone());
                assert!(old.is_none());
            }

            for (label, label1_ty) in &labels1_map {
                let label2_ty = match labels2_map.remove(label) {
                    Some(label2_ty) => label2_ty,
                    None => return false,
                };
                if !match_named_ty(label1_ty, &label2_ty, substs) {
                    return false;
                }
            }

            let ext_var = match extension {
                Some(ext_var) => ext_var,
                None => return labels2_map.is_empty(),
            };

            substs.insert(ext_var.clone(), mono::Type::Variant { alts: labels2_map });

            true
        }

        (ast::Type::Var(var), ty) => {
            // This overrides previous mappings generated for the same impl match. E.g.
            // Iterator.next takes [iter, item]
            // Impl args = [RangeIterator[t],   t]
            // Args      = [RangeIterator[U32], U32]
            // However since the program is well-typed it should be OK.
            substs.insert(var.clone(), ty.clone());
            true
        }

        _ => false,
    }
}

fn match_named_ty(
    trait_ty: &ast::NamedType,
    arg_ty: &mono::NamedType,
    substs: &mut HashMap<Id, mono::Type>,
) -> bool {
    if trait_ty.name != arg_ty.name {
        return false;
    }
    debug_assert_eq!(trait_ty.args.len(), arg_ty.args.len());

    for (arg1, arg2) in trait_ty.args.iter().zip(arg_ty.args.iter()) {
        if !match_(&arg1.node, arg2, substs) {
            return false;
        }
    }

    true
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Types

/// Monomorphise a type-checking type.
fn mono_tc_ty(
    ty: &Ty,
    ty_map: &HashMap<Id, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> mono::Type {
    match ty.clone() {
        // TODO: When defaulting exception types we should use empty variant instead of record, to
        // indicate that the function doesn't throw.
        Ty::UVar(var) => match var.kind() {
            Kind::Star => mono::Type::unit(),
            Kind::Row(RecordOrVariant::Record) => mono::Type::unit(),
            Kind::Row(RecordOrVariant::Variant) => mono::Type::Variant {
                alts: Default::default(),
            },
        },

        Ty::Con(con, _kind) => {
            if let Some(ty) = ty_map.get(&con) {
                return ty.clone();
            }

            let ty_decl = poly_pgm
                .ty
                .get(&con)
                .unwrap_or_else(|| panic!("Unknown type constructor {con}"));

            mono::Type::Named(mono::NamedType {
                name: mono_ty_decl(ty_decl, &[], poly_pgm, mono_pgm),
                args: vec![],
            })
        }

        Ty::App(con, args, _kind) => {
            let ty_decl = poly_pgm.ty.get(&con).unwrap();
            let mono_args: Vec<mono::Type> = args
                .iter()
                .map(|arg| mono_tc_ty(arg, ty_map, poly_pgm, mono_pgm))
                .collect();
            let mono_ty_decl = mono_ty_decl(ty_decl, &mono_args, poly_pgm, mono_pgm);
            mono::Type::Named(mono::NamedType {
                name: mono_ty_decl,
                args: mono_args,
            })
        }

        // TODO: This should be a panic. After type checking, type parameters of the function will
        // be rigid type variables, which are represented as `Ty::Con`, and those will be mapped to
        // mono types in the `Ty::Con` case above.
        Ty::QVar(var, _kind) => ty_map.get(&var).unwrap().clone(),

        Ty::Fun {
            args,
            ret,
            exceptions,
        } => mono::Type::Fn(mono::FnType {
            args: match args {
                FunArgs::Positional(args) => mono::FunArgs::Positional(
                    args.iter()
                        .map(|arg| mono_tc_ty(arg, ty_map, poly_pgm, mono_pgm))
                        .collect(),
                ),
                FunArgs::Named(args) => mono::FunArgs::Named(
                    args.iter()
                        .map(|(arg_name, arg)| {
                            (
                                arg_name.clone(),
                                mono_tc_ty(arg, ty_map, poly_pgm, mono_pgm),
                            )
                        })
                        .collect(),
                ),
            },
            ret: Box::new(mono_tc_ty(&ret, ty_map, poly_pgm, mono_pgm)),
            exn: Box::new(
                exceptions
                    .map(|ty| mono_tc_ty(&ty, ty_map, poly_pgm, mono_pgm))
                    .unwrap_or(mono::Type::empty()),
            ),
        }),

        Ty::Anonymous {
            labels,
            extension,
            kind,
            is_row: _,
        } => match kind {
            crate::type_checker::RecordOrVariant::Record => {
                let mut all_fields: OrdMap<Id, mono::Type> = Default::default();

                for (field, field_ty) in labels {
                    let field_mono_ty = mono_tc_ty(&field_ty, ty_map, poly_pgm, mono_pgm);
                    all_fields.insert(field, field_mono_ty);
                }

                if let Some(ty) = extension {
                    match &*ty {
                        Ty::Con(con, _kind) => {
                            let ext = ty_map.get(con).unwrap();
                            match ext {
                                mono::Type::Record { fields } => {
                                    all_fields
                                        .extend(fields.iter().map(|(k, v)| (k.clone(), v.clone())));
                                }
                                _ => panic!(),
                            }
                        }

                        Ty::UVar(var) => {
                            assert!(var.link().is_none());
                        }

                        other => todo!("Weird row extension {:?}", other),
                    }
                }

                mono::Type::Record { fields: all_fields }
            }

            crate::type_checker::RecordOrVariant::Variant => {
                let mut all_alts: OrdMap<Id, mono::NamedType> = Default::default();

                for (id, ty) in labels.iter() {
                    let ty = mono_tc_ty(ty, ty_map, poly_pgm, mono_pgm);
                    match ty {
                        mono::Type::Named(named_ty) => {
                            let old = all_alts.insert(id.clone(), named_ty.clone());
                            assert!(match old {
                                Some(old) => old == named_ty,
                                None => true,
                            });
                        }
                        _ => panic!(),
                    }
                }

                if let Some(ty) = extension {
                    match &*ty {
                        Ty::Con(con, _kind) => {
                            let ext = ty_map.get(con).unwrap();
                            match ext {
                                mono::Type::Variant { alts } => {
                                    all_alts
                                        .extend(alts.iter().map(|(k, v)| (k.clone(), v.clone())));
                                }
                                _ => panic!(),
                            }
                        }

                        Ty::UVar(var) => {
                            assert!(var.link().is_none());
                        }

                        other => todo!("Weird row extension {:?}", other),
                    }
                }

                mono::Type::Variant { alts: all_alts }
            }
        },
    }
}

fn mono_ast_ty(
    ty: &ast::Type,
    ty_map: &HashMap<Id, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> mono::Type {
    match ty {
        ast::Type::Named(ast::NamedType { name: con, args }) => {
            let ty_decl = poly_pgm.ty.get(con).unwrap_or_else(|| panic!("{}", con));
            let mono_args: Vec<mono::Type> = args
                .iter()
                .map(|arg| mono_ast_ty(&arg.node, ty_map, poly_pgm, mono_pgm))
                .collect();
            let mono_ty_decl_id = mono_ty_decl(ty_decl, &mono_args, poly_pgm, mono_pgm);
            mono::Type::Named(mono::NamedType {
                name: mono_ty_decl_id,
                args: mono_args,
            })
        }

        ast::Type::Var(var) => ty_map.get(var).unwrap().clone(),

        ast::Type::Record {
            fields,
            extension,
            is_row,
        } => {
            assert!(!*is_row);

            let mut names: HashSet<&Id> = Default::default();
            for (field_name, _field_ty) in fields {
                let new = names.insert(field_name);
                if !new {
                    panic!("Record has duplicate fields: {fields:?}");
                }
            }

            let mut fields: OrdMap<Id, mono::Type> = fields
                .iter()
                .map(|(field_name, field_ty)| {
                    (
                        field_name.clone(),
                        mono_ast_ty(field_ty, ty_map, poly_pgm, mono_pgm),
                    )
                })
                .collect();

            if let Some(extension) = extension {
                match ty_map.get(extension) {
                    Some(mono::Type::Record {
                        fields: extra_fields,
                    }) => {
                        fields.extend(extra_fields.iter().map(|(k, v)| (k.clone(), v.clone())));
                    }
                    other => panic!("Record extension is not a record: {other:?}"),
                }
            }

            mono::Type::Record { fields }
        }

        ast::Type::Variant {
            alts,
            extension,
            is_row,
        } => {
            assert!(!*is_row);

            let mut labels: HashSet<&Id> = Default::default();
            for ast::NamedType { name, .. } in alts {
                let new = labels.insert(name);
                if !new {
                    panic!("Variant has duplicate labels: {alts:?}");
                }
            }

            let mut alts: OrdMap<Id, mono::NamedType> = alts
                .iter()
                .map(|ast::NamedType { name, args }| {
                    (
                        name.clone(),
                        mono::NamedType {
                            name: name.clone(),
                            args: args
                                .iter()
                                .map(|ty| mono_ast_ty(&ty.node, ty_map, poly_pgm, mono_pgm))
                                .collect(),
                        },
                    )
                })
                .collect();

            if let Some(extension) = extension {
                match ty_map.get(extension) {
                    Some(mono::Type::Variant { alts: extra_alts }) => {
                        alts.extend(extra_alts.iter().map(|(k, v)| (k.clone(), v.clone())));
                    }
                    Some(other) => panic!("Variant extension is not a variant: {other:?}"),
                    None => panic!(
                        "Variant extension is not in ty map: {extension}\n\
                        Ty map = {ty_map:#?}"
                    ),
                }
            }

            mono::Type::Variant { alts }
        }

        ast::Type::Fn(ast::FnType {
            args,
            ret,
            exceptions,
        }) => mono::Type::Fn(mono::FnType {
            args: mono::FunArgs::Positional(
                args.iter()
                    .map(|arg| mono_ast_ty(&arg.node, ty_map, poly_pgm, mono_pgm))
                    .collect(),
            ),
            ret: Box::new(
                ret.as_ref()
                    .map(|ret| mono_ast_ty(&ret.node, ty_map, poly_pgm, mono_pgm))
                    .unwrap_or_else(mono::Type::unit),
            ),
            exn: Box::new(
                exceptions
                    .as_ref()
                    .map(|exn| mono_ast_ty(&exn.node, ty_map, poly_pgm, mono_pgm))
                    .unwrap_or_else(mono::Type::empty),
            ),
        }),
    }
}

/// Monomorphise a type declaration. Returns the name of the mono type.
fn mono_ty_decl(
    ty_decl: &ast::TypeDecl,
    args: &[mono::Type],
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> Id {
    assert_eq!(ty_decl.type_params.len(), args.len());

    let mono_ty_id = ty_decl.name.clone();

    // Check if we've already monomorphised this type.
    if let Some(mono_decl) = mono_pgm
        .ty
        .get(&ty_decl.name)
        .and_then(|arg_map| arg_map.get(args))
    {
        return mono_decl.name.clone();
    }

    // Add current type to mono_pgm without a RHS to avoid looping.
    mono_pgm.ty.entry(ty_decl.name.clone()).or_default().insert(
        args.to_vec(),
        mono::TypeDecl {
            name: mono_ty_id.clone(),
            rhs: None,
        },
    );

    // Maps type parameters of the type to type arguments.
    let ty_map: HashMap<Id, mono::Type> = ty_decl
        .type_params
        .iter()
        .cloned()
        .zip(args.iter().cloned())
        .collect();

    let rhs: Option<mono::TypeDeclRhs> = ty_decl.rhs.as_ref().map(|rhs| match rhs {
        ast::TypeDeclRhs::Sum(cons) => mono::TypeDeclRhs::Sum(
            cons.iter()
                .map(|con| mono_con(con, &ty_map, poly_pgm, mono_pgm))
                .collect(),
        ),

        ast::TypeDeclRhs::Product(fields) => {
            mono::TypeDeclRhs::Product(mono_fields(fields, &ty_map, poly_pgm, mono_pgm))
        }
    });

    mono_pgm.ty.get_mut(&ty_decl.name).unwrap().insert(
        args.to_vec(),
        mono::TypeDecl {
            name: mono_ty_id.clone(),
            rhs,
        },
    );

    mono_ty_id
}

fn mono_con(
    con: &ast::ConDecl,
    ty_map: &HashMap<Id, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> mono::ConDecl {
    mono::ConDecl {
        name: con.name.clone(),
        fields: mono_fields(&con.fields, ty_map, poly_pgm, mono_pgm),
    }
}

fn mono_fields(
    fields: &ast::ConFields,
    ty_map: &HashMap<Id, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> mono::ConFields {
    match fields {
        ast::ConFields::Empty => mono::ConFields::Empty,

        ast::ConFields::Named(fields) => mono::ConFields::Named(
            fields
                .iter()
                .map(|(name, ty)| {
                    (
                        name.clone(),
                        mono_ast_ty(&ty.node, ty_map, poly_pgm, mono_pgm),
                    )
                })
                .collect(),
        ),

        ast::ConFields::Unnamed(fields) => mono::ConFields::Unnamed(
            fields
                .iter()
                .map(|ty| mono_ast_ty(&ty.node, ty_map, poly_pgm, mono_pgm))
                .collect(),
        ),
    }
}

fn get_record_ty(ty: mono::Type, loc: &ast::Loc) -> OrdMap<Id, mono::Type> {
    match ty {
        mono::Type::Record { fields } => fields,

        other @ (mono::Type::Named(_) | mono::Type::Variant { .. } | mono::Type::Fn(_)) => {
            panic!(
                "{}: BUG: Record expression with non-record type: {}",
                loc_display(loc),
                other
            )
        }

        mono::Type::Never => {
            // This can't happen as we only infer `Never` during lowering.
            panic!()
        }
    }
}

fn get_variant_ty(ty: mono::Type, loc: &ast::Loc) -> OrdMap<Id, mono::NamedType> {
    match ty {
        mono::Type::Variant { alts } => alts,

        other @ (mono::Type::Named(_) | mono::Type::Record { .. } | mono::Type::Fn(_)) => {
            panic!(
                "{}: BUG: Variant expression with non-record type: {}",
                loc_display(loc),
                other
            )
        }

        mono::Type::Never => {
            // This can't happen as we only infer `Never` during lowering.
            panic!()
        }
    }
}
