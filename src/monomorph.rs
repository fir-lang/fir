use crate::ast::{self, Name, Named};
use crate::collections::*;
use crate::interpolation::StrPart;
use crate::mono_ast as mono;
use crate::mono_ast::MonoPgm;
use crate::type_checker::id::builtins;
use crate::type_checker::{FunArgs, Kind, RecordOrVariant, Ty};
use crate::utils::*;

/// The program in front-end syntax, converted to a graph for efficient and easy lookups.
#[derive(Debug)]
struct PolyPgm {
    traits: HashMap<Name, PolyTrait>,

    /// Top-level functions, e.g. `foo(x: U32): ...`.
    top: HashMap<Name, ast::FunDecl>,

    /// Associated functions without `self` arguments, e.g. `Type.foo(x: U32): ...`.
    associated: HashMap<Name, HashMap<Name, ast::FunDecl>>,

    /// Associated functions with `self` arguments, e.g. `Type.bar(self, x: U32): ...`.
    method: HashMap<Name, HashMap<Name, ast::FunDecl>>,

    ty: HashMap<Name, ast::TypeDecl>,
}

/// A trait, with implementations.
#[derive(Debug, Default)]
struct PolyTrait {
    /// QVars of trait.
    ty_args: Vec<(Name, Kind)>,

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
    type_params: Vec<(Name, Kind)>,

    /// Type arguments of the trait.
    ///
    /// In the example above: `[Map[iter, a, b], b]`.
    tys: Vec<ast::Type>,

    methods: Vec<ast::FunDecl>,

    /// Associated type definitions, e.g. `type Item = t`.
    assoc_tys: Vec<(Name, ast::Type)>,
    // We don't care about predicates, those are for type checking.
    // If a trait use type checks, then we know there will be a match in trait env during monomorph.
}

fn pgm_to_poly_pgm(pgm: Vec<ast::TopDecl>) -> PolyPgm {
    let mut traits: HashMap<Name, PolyTrait> = Default::default();
    let mut top: HashMap<Name, ast::FunDecl> = Default::default();
    let mut associated: HashMap<Name, HashMap<Name, ast::FunDecl>> = Default::default();
    let mut method: HashMap<Name, HashMap<Name, ast::FunDecl>> = Default::default();
    let mut ty: HashMap<Name, ast::TypeDecl> = Default::default();

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
                            .map(|type_param| type_param.name.node.clone())
                            .zip(trait_decl.node.type_param_kinds.iter().cloned())
                            .collect();
                    }
                    Entry::Vacant(entry) => {
                        entry.insert(PolyTrait {
                            ty_args: trait_decl
                                .node
                                .type_params
                                .iter()
                                .map(|type_param| type_param.name.node.clone())
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
                            .filter_map(|item| match item {
                                ast::ImplDeclItem::Type { .. } => None,
                                ast::ImplDeclItem::Fun(fun) => Some(fun.node.clone()),
                            })
                            .collect(),
                        assoc_tys: impl_decl
                            .node
                            .items
                            .iter()
                            .filter_map(|item| match item {
                                ast::ImplDeclItem::Type { assoc_ty, rhs } => {
                                    Some((assoc_ty.node.clone(), rhs.node.clone()))
                                }
                                ast::ImplDeclItem::Fun(_) => None,
                            })
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

pub fn monomorphise(pgm: &ast::Module, main: &str) -> MonoPgm {
    let poly_pgm = pgm_to_poly_pgm(pgm.decls.iter().map(|decl| decl.node.clone()).collect());
    let mut mono_pgm = MonoPgm::default();

    // Copy types used by the interpreter built-ins.
    for ty in [
        Ty::Con(builtins::BOOL(), Kind::Star),
        Ty::Con(builtins::CHAR(), Kind::Star),
        Ty::Con(builtins::STR(), Kind::Star),
        Ty::Con(builtins::ORDERING(), Kind::Star),
        Ty::Con(builtins::I8(), Kind::Star),
        Ty::Con(builtins::U8(), Kind::Star),
        Ty::Con(builtins::I32(), Kind::Star),
        Ty::Con(builtins::U32(), Kind::Star),
        Ty::App(
            builtins::ARRAY(),
            vec![Ty::Con(builtins::I8(), Kind::Star)],
            Kind::Star,
        ),
        Ty::App(
            builtins::ARRAY(),
            vec![Ty::Con(builtins::U8(), Kind::Star)],
            Kind::Star,
        ),
        Ty::App(
            builtins::ARRAY(),
            vec![Ty::Con(builtins::I32(), Kind::Star)],
            Kind::Star,
        ),
        Ty::App(
            builtins::ARRAY(),
            vec![Ty::Con(builtins::U32(), Kind::Star)],
            Kind::Star,
        ),
        Ty::App(
            builtins::ARRAY(),
            vec![Ty::Con(builtins::I64(), Kind::Star)],
            Kind::Star,
        ),
        Ty::App(
            builtins::ARRAY(),
            vec![Ty::Con(builtins::U64(), Kind::Star)],
            Kind::Star,
        ),
    ] {
        mono_tc_ty(&ty, &Default::default(), &poly_pgm, &mut mono_pgm);
    }

    let main = poly_pgm
        .top
        .get(main)
        .unwrap_or_else(|| panic!("Main function `{main}` not defined"));

    mono_top_fn(main, &[], &poly_pgm, &mut mono_pgm);

    mono_pgm
}

fn mono_top_fn(
    fun_decl: &ast::FunDecl,
    ty_args: &[mono::Type],
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) {
    assert_eq!(fun_decl.sig.context.type_params.len(), ty_args.len());

    let ty_map: HashMap<Name, mono::Type> = fun_decl
        .sig
        .context
        .type_params
        .iter()
        .map(|(ty_param, _)| ty_param.clone())
        .zip(ty_args.iter().cloned())
        .collect();

    let mut params: Vec<(Name, ast::L<mono::Type>)> =
        Vec::with_capacity(fun_decl.sig.params.len() + 1);

    let mut locals: ScopeSet<Name> = Default::default();

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
                Name::new_static("self"),
                ast::L::new_dummy(mono::Type::Named(mono::NamedType {
                    name: self_ty_con,
                    args: vec![],
                })),
            ));
            locals.insert(Name::new_static("self"));
        }
        ast::SelfParam::Explicit(self_ty) => {
            let self_mono_ty = mono_l_ty(self_ty, &ty_map, poly_pgm, mono_pgm);
            params.push((Name::new_static("self"), self_mono_ty));
            locals.insert(Name::new_static("self"));
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
    ty_map: &HashMap<Name, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    locals: &mut ScopeSet<Name>,
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
    ty_map: &HashMap<Name, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    locals: &mut ScopeSet<Name>,
    loc: &ast::Loc,
) -> mono::Expr {
    match expr {
        ast::Expr::Var(ast::VarExpr {
            id: var,
            user_ty_args: _,
            ty_args,
            inferred_ty,
        }) => {
            if locals.is_bound(var) {
                // Local variable, cannot be polymorphic.
                assert!(ty_args.is_empty());
                return mono::Expr::LocalVar(
                    var.clone(),
                    mono_tc_ty(inferred_ty.as_ref().unwrap(), ty_map, poly_pgm, mono_pgm),
                );
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
                ty: mono_tc_ty(inferred_ty.as_ref().unwrap(), ty_map, poly_pgm, mono_pgm),
            })
        }

        ast::Expr::FieldSel(ast::FieldSelExpr {
            object,
            field,
            user_ty_args: _,
            inferred_ty,
        }) => mono::Expr::FieldSel(mono::FieldSelExpr {
            object: mono_bl_expr(object, ty_map, poly_pgm, mono_pgm, locals),
            field: field.clone(),
            ty: mono_tc_ty(inferred_ty.as_ref().unwrap(), ty_map, poly_pgm, mono_pgm),
        }),

        ast::Expr::MethodSel(ast::MethodSelExpr {
            object,       // receiver
            method_ty_id, // trait of type that the method belongs to
            method,       // method or associated function name
            ty_args,      // function type arguments
            inferred_ty,
        }) => {
            let inferred_ty = mono_tc_ty(inferred_ty.as_ref().unwrap(), ty_map, poly_pgm, mono_pgm);

            let mono_ty_args: Vec<mono::Type> = ty_args
                .iter()
                .map(|ty| mono_tc_ty(ty, ty_map, poly_pgm, mono_pgm))
                .collect();

            mono_method(
                method_ty_id.name(),
                method,
                &mono_ty_args,
                poly_pgm,
                mono_pgm,
                loc,
            );

            let mono_object = mono_bl_expr(object, ty_map, poly_pgm, mono_pgm, locals);

            let mono_object_ty = mono_tc_ty(
                object.node.inferred_ty().as_ref().unwrap(),
                ty_map,
                poly_pgm,
                mono_pgm,
            );

            /*
            <receiver>.<method>

            ==>

            do:
                let receiver = <receiver>
                \(...args): <receiver_type>.<method>(reciver, ...args)
            */

            let mono_fun = mono_pgm
                .associated
                .get(method_ty_id.name())
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

            let closure_params: Vec<(Name, mono::L<mono::Type>)> = mono_fun_args
                .iter()
                .skip(1) // skip receiver
                .enumerate()
                .map(|(i, arg_ty)| {
                    (
                        Name::new(format!("$arg{}$", i)),
                        mono::L {
                            loc: loc.clone(),
                            node: arg_ty.clone(),
                        },
                    )
                })
                .collect();

            let receiver_id = Name::new_static("$receiver$");

            let assoc_fn_args: Vec<mono::CallArg> =
                std::iter::once((receiver_id.clone(), mono_object_ty.clone()))
                    .chain(
                        closure_params
                            .iter()
                            .map(|(arg, ty)| (arg.clone(), ty.node.clone())),
                    )
                    .map(|(arg, ty)| mono::CallArg {
                        name: None,
                        expr: ast::L {
                            loc: loc.clone(),
                            node: mono::Expr::LocalVar(arg, ty),
                        },
                    })
                    .collect();

            mono::Expr::Do(
                vec![
                    mono::L {
                        loc: loc.clone(),
                        node: mono::Stmt::Let(mono::LetStmt {
                            lhs: mono::L {
                                loc: loc.clone(),
                                node: mono::Pat::Var(mono::VarPat {
                                    var: Name::new_static("$receiver$"),
                                    ty: mono_object_ty,
                                    refined: None,
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
                                            ty_id: method_ty_id.name().clone(),
                                            member: method.clone(),
                                            ty_args: mono_ty_args,
                                            ty: mono::Type::Fn(mono_fun.sig.ty()),
                                        }),
                                    }),
                                    args: assoc_fn_args,
                                    splice: None,
                                    ty: inferred_ty.clone(),
                                })),
                            }],
                        })),
                    },
                ],
                inferred_ty,
            )
        }

        ast::Expr::ConSel(ast::Con {
            ty,
            con,
            user_ty_args: _,
            ty_args,
            inferred_ty,
        }) => {
            let inferred_ty = mono_tc_ty(inferred_ty.as_ref().unwrap(), ty_map, poly_pgm, mono_pgm);
            match con {
                Some(con) => {
                    let poly_ty_decl = poly_pgm.ty.get(ty).unwrap();

                    let mono_ty_args = ty_args
                        .iter()
                        .map(|ty| mono_tc_ty(ty, ty_map, poly_pgm, mono_pgm))
                        .collect::<Vec<_>>();

                    let mono_ty_id = mono_ty_decl(poly_ty_decl, &mono_ty_args, poly_pgm, mono_pgm);

                    mono::Expr::ConSel(mono::Con {
                        ty_id: mono_ty_id,
                        con: Some(con.clone()),
                        ty_args: mono_ty_args,
                        ty: inferred_ty,
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
                        ty_id: mono_ty_id,
                        con: None,
                        ty_args: mono_ty_args,
                        ty: inferred_ty,
                    })
                }
            }
        }

        ast::Expr::AssocFnSel(ast::AssocFnSelExpr {
            ty,
            ty_user_ty_args: _,
            member,
            user_ty_args: _,
            ty_args,
            inferred_ty,
        }) => {
            let inferred_ty = mono_tc_ty(inferred_ty.as_ref().unwrap(), ty_map, poly_pgm, mono_pgm);

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
                    ty_id: ty.clone(),
                    member: member.clone(),
                    ty_args: mono_ty_args,
                    ty: inferred_ty,
                });
            }

            // Check traits.
            if poly_pgm.traits.contains_key(ty) {
                mono_method(ty, member, &mono_ty_args, poly_pgm, mono_pgm, loc);
                return mono::Expr::AssocFnSel(mono::AssocFnSelExpr {
                    ty_id: ty.clone(),
                    member: member.clone(),
                    ty_args: mono_ty_args,
                    ty: inferred_ty,
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

        ast::Expr::Call(ast::CallExpr {
            fun,
            args,
            splice,
            inferred_ty,
        }) => mono::Expr::Call(mono::CallExpr {
            fun: mono_bl_expr(fun, ty_map, poly_pgm, mono_pgm, locals),
            args: args
                .iter()
                .map(|ast::CallArg { name, expr }| mono::CallArg {
                    name: name.clone(),
                    expr: mono_l_expr(expr, ty_map, poly_pgm, mono_pgm, locals),
                })
                .collect(),
            splice: splice
                .as_ref()
                .map(|expr| mono_bl_expr(expr, ty_map, poly_pgm, mono_pgm, locals)),
            ty: mono_tc_ty(inferred_ty.as_ref().unwrap(), ty_map, poly_pgm, mono_pgm),
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

        ast::Expr::BinOp(ast::BinOpExpr {
            left,
            right,
            op: ast::BinOp::Or,
        }) => mono::Expr::BoolOr(
            mono_bl_expr(left, ty_map, poly_pgm, mono_pgm, locals),
            mono_bl_expr(right, ty_map, poly_pgm, mono_pgm, locals),
        ),

        ast::Expr::BinOp(ast::BinOpExpr {
            left,
            right,
            op: ast::BinOp::And,
        }) => mono::Expr::BoolAnd(
            mono_bl_expr(left, ty_map, poly_pgm, mono_pgm, locals),
            mono_bl_expr(right, ty_map, poly_pgm, mono_pgm, locals),
        ),

        ast::Expr::BinOp(ast::BinOpExpr { op, .. }) => {
            panic!("{}: Non-desugared binop: {:?}", loc_display(loc), op);
        }

        ast::Expr::UnOp(ast::UnOpExpr { op, expr: _ }) => {
            panic!("{}: Non-desugared unop: {:?}", loc_display(loc), op)
        }

        ast::Expr::Return(ast::ReturnExpr { expr, inferred_ty }) => mono::Expr::Return(
            mono_bl_expr(expr, ty_map, poly_pgm, mono_pgm, locals),
            mono_tc_ty(inferred_ty.as_ref().unwrap(), ty_map, poly_pgm, mono_pgm),
        ),

        ast::Expr::Match(ast::MatchExpr {
            scrutinee,
            alts,
            inferred_ty,
        }) => mono::Expr::Match(mono::MatchExpr {
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
            ty: mono_tc_ty(inferred_ty.as_ref().unwrap(), ty_map, poly_pgm, mono_pgm),
        }),

        ast::Expr::If(ast::IfExpr {
            branches,
            else_branch,
            inferred_ty,
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
            ty: mono_tc_ty(inferred_ty.as_ref().unwrap(), ty_map, poly_pgm, mono_pgm),
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
                        FunArgs::Positional { args } => args,
                        FunArgs::Named { args: _, .. } => panic!(),
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

        ast::Expr::Do(ast::DoExpr { stmts, inferred_ty }) => {
            let inferred_ty = mono_tc_ty(inferred_ty.as_ref().unwrap(), ty_map, poly_pgm, mono_pgm);
            mono::Expr::Do(
                mono_l_stmts(stmts, ty_map, poly_pgm, mono_pgm, locals),
                inferred_ty,
            )
        }

        ast::Expr::Seq { .. } => panic!("Seq expr should've been desugared"),

        ast::Expr::Record(ast::RecordExpr {
            fields,
            splice,
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

            splice: splice
                .as_ref()
                .map(|expr| mono_bl_expr(expr, ty_map, poly_pgm, mono_pgm, locals)),

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
    method_ty_id: &Name,    // type that the method belonds to: `trait` or `type`
    method_id: &Name,       // method name
    ty_args: &[mono::Type], // method type arguments, including the trait or type's
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    loc: &ast::Loc,
) {
    // RecRowToList.rowToList: synthesize a method that converts a record to a list.
    if *method_ty_id == "RecRowToList" && *method_id == "rowToList" {
        return synthesize_row_to_list(ty_args, poly_pgm, mono_pgm);
    }

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

                let mut params: Vec<(Name, ast::L<mono::Type>)> =
                    Vec::with_capacity(method.sig.params.len() + 1);

                let mut locals: ScopeSet<Name> = Default::default();

                match &method.sig.self_ {
                    ast::SelfParam::No => {}
                    ast::SelfParam::Implicit => panic!(),
                    ast::SelfParam::Explicit(self_ty) => {
                        let self_mono_ty = mono_l_ty(self_ty, &substs, poly_pgm, mono_pgm);
                        params.push((Name::new_static("self"), self_mono_ty));
                        locals.insert(Name::new_static("self"));
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

        let ty_map: HashMap<Name, mono::Type> = method
            .sig
            .context
            .type_params
            .iter()
            .map(|(ty_param, _)| ty_param.clone())
            .zip(ty_args.iter().cloned())
            .collect();

        let mut params: Vec<(Name, ast::L<mono::Type>)> =
            Vec::with_capacity(method.sig.params.len() + 1);

        let mut locals: ScopeSet<Name> = Default::default();

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
                    Name::new_static("self"),
                    ast::L::new_dummy(mono::Type::Named(mono::NamedType {
                        name: self_ty_con,
                        args: vec![],
                    })),
                ));
                locals.insert(Name::new_static("self"));
            }
            ast::SelfParam::Explicit(self_ty) => {
                let self_mono_ty = mono_l_ty(self_ty, &ty_map, poly_pgm, mono_pgm);
                params.push((Name::new_static("self"), self_mono_ty));
                locals.insert(Name::new_static("self"));
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
    ty_map: &HashMap<Name, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    locals: &mut ScopeSet<Name>,
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
    ty_map: &HashMap<Name, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    locals: &mut ScopeSet<Name>,
) -> Box<ast::L<mono::Expr>> {
    Box::new(
        expr.map_as_ref(|expr_| mono_expr(expr_, ty_map, poly_pgm, mono_pgm, locals, &expr.loc)),
    )
}

fn mono_l_expr(
    expr: &ast::L<ast::Expr>,
    ty_map: &HashMap<Name, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    locals: &mut ScopeSet<Name>,
) -> ast::L<mono::Expr> {
    expr.map_as_ref(|expr_| mono_expr(expr_, ty_map, poly_pgm, mono_pgm, locals, &expr.loc))
}

fn mono_pat(
    pat: &ast::Pat,
    ty_map: &HashMap<Name, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    locals: &mut ScopeSet<Name>,
    loc: &ast::Loc,
) -> mono::Pat {
    match pat {
        ast::Pat::Var(pat) => mono::Pat::Var(mono_var_pat(pat, ty_map, poly_pgm, mono_pgm, locals)),

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
                    inferred_ty,
                },
            fields,
            rest,
        }) => {
            let inferred_ty = mono_tc_ty(inferred_ty.as_ref().unwrap(), ty_map, poly_pgm, mono_pgm);

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
                    ty_id: mono_ty_id,
                    con: con.clone(),
                    ty_args: mono_ty_args,
                    ty: inferred_ty,
                },
                fields: mono_fields,
                rest: mono_rest_pat(rest, ty_map, poly_pgm, mono_pgm, locals),
            })
        }

        ast::Pat::Record(ast::RecordPat {
            fields,
            rest,
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
            rest: mono_rest_pat(rest, ty_map, poly_pgm, mono_pgm, locals),
        }),

        ast::Pat::Variant(ast::VariantPat {
            pat,
            inferred_ty,
            inferred_pat_ty,
        }) => mono::Pat::Variant(mono::VariantPat {
            pat: mono_bl_pat(pat, ty_map, poly_pgm, mono_pgm, locals),
            variant_ty: get_variant_ty(
                mono_tc_ty(inferred_ty.as_ref().unwrap(), ty_map, poly_pgm, mono_pgm),
                loc,
            ),
            pat_ty: mono_tc_ty(
                inferred_pat_ty.as_ref().unwrap(),
                ty_map,
                poly_pgm,
                mono_pgm,
            ),
        }),
    }
}

fn mono_var_pat(
    ast::VarPat { var, ty, refined }: &ast::VarPat,
    ty_map: &HashMap<Name, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    locals: &mut ScopeSet<Name>,
) -> mono::VarPat {
    let mono_ty = mono_tc_ty(ty.as_ref().unwrap(), ty_map, poly_pgm, mono_pgm);
    let refined = refined
        .as_ref()
        .map(|refined| mono_tc_ty(refined, ty_map, poly_pgm, mono_pgm));
    locals.insert(var.clone());
    mono::VarPat {
        var: var.clone(),
        ty: mono_ty,
        refined,
    }
}

fn mono_rest_pat(
    rest: &ast::RestPat,
    ty_map: &HashMap<Name, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    locals: &mut ScopeSet<Name>,
) -> mono::RestPat {
    match rest {
        ast::RestPat::Ignore => mono::RestPat::Ignore,
        ast::RestPat::Bind(var_pat) => {
            mono::RestPat::Bind(mono_var_pat(var_pat, ty_map, poly_pgm, mono_pgm, locals))
        }
        ast::RestPat::No => mono::RestPat::No,
    }
}

fn mono_l_pat(
    pat: &ast::L<ast::Pat>,
    ty_map: &HashMap<Name, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    locals: &mut ScopeSet<Name>,
) -> ast::L<mono::Pat> {
    pat.map_as_ref(|pat_| mono_pat(pat_, ty_map, poly_pgm, mono_pgm, locals, &pat.loc))
}

fn mono_bl_pat(
    pat: &ast::L<ast::Pat>,
    ty_map: &HashMap<Name, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    locals: &mut ScopeSet<Name>,
) -> Box<ast::L<mono::Pat>> {
    Box::new(mono_l_pat(pat, ty_map, poly_pgm, mono_pgm, locals))
}

fn mono_named_l_pat(
    pat: &Named<ast::L<ast::Pat>>,
    ty_map: &HashMap<Name, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    locals: &mut ScopeSet<Name>,
) -> Named<ast::L<mono::Pat>> {
    pat.map_as_ref(|pat| mono_l_pat(pat, ty_map, poly_pgm, mono_pgm, locals))
}

fn mono_l_ty(
    ty: &ast::L<ast::Type>,
    ty_map: &HashMap<Name, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> ast::L<mono::Type> {
    ty.map_as_ref(|ty| mono_ast_ty(ty, ty_map, poly_pgm, mono_pgm))
}

fn mono_opt_l_ty(
    ty: &Option<ast::L<ast::Type>>,
    ty_map: &HashMap<Name, mono::Type>,
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
) -> Option<HashMap<Name, mono::Type>> {
    debug_assert_eq!(ty_args.len(), trait_impl.tys.len(), "{ty_args:?}");

    let mut substs: HashMap<Name, mono::Type> = Default::default();
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
    substs: &mut HashMap<Name, mono::Type>,
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
            let fields1_map: HashMap<&Name, &ast::Type> = fields1
                .iter()
                .map(|(field_name, field_ty)| (field_name, field_ty))
                .collect();

            let mut fields2_map: HashMap<&Name, &mono::Type> = fields2.iter().collect();

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

            if let Some(ext) = extension.as_ref() {
                let ext_var = match &ext.node {
                    ast::Type::Var(id) => id,
                    _ => panic!("BUG: Non-variable record extension in match_"),
                };
                substs.insert(
                    ext_var.clone(),
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
            let mut labels1_map: HashMap<Name, ast::NamedType> = Default::default();
            for alt1_ty in alts1 {
                let old = labels1_map.insert(alt1_ty.name.clone(), alt1_ty.clone());
                assert!(old.is_none());
            }

            let mut labels2_map: OrdMap<Name, mono::NamedType> = Default::default();
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

            let ext_var = match extension.as_ref().map(|e| &e.node) {
                Some(ast::Type::Var(id)) => id,
                None => return labels2_map.is_empty(),
                _ => panic!("BUG: Non-variable variant extension in match_"),
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
    substs: &mut HashMap<Name, mono::Type>,
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

/// Resolve an associated type selection.
///
/// Given a trait name, concrete type args, and an associated type name, find the matching impl and
/// return the monomorphized associated type.
fn resolve_assoc_ty(
    trait_name: &Name,
    trait_args: &[mono::Type],
    assoc_ty: &Name,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> mono::Type {
    // RecRowToList[row].List: synthesize the List type from the row's fields.
    if *trait_name == "RecRowToList" && *assoc_ty == "List" {
        let fields = match &trait_args[0] {
            mono::Type::Record { fields } => fields,
            other => panic!("RecRowToList type arg is not a record: {other:?}"),
        };
        return row_to_list_type(fields, poly_pgm, mono_pgm);
    }

    let poly_trait = poly_pgm
        .traits
        .get(trait_name)
        .unwrap_or_else(|| panic!("Unknown trait {} in associated type selection", trait_name));

    for impl_ in &poly_trait.impls {
        if let Some(substs) = match_trait_impl(trait_args, impl_) {
            for (name, rhs_ty) in &impl_.assoc_tys {
                if name == assoc_ty {
                    return mono_ast_ty(rhs_ty, &substs, poly_pgm, mono_pgm);
                }
            }
        }
    }

    panic!(
        "No matching impl for {}.{} with args {:?}",
        trait_name, assoc_ty, trait_args
    )
}

/// Build the `List` type for `RecRowToList`: `List[RecordField[T1], List[..., []]]`.
///
/// This is the same function as `crate::type_checker::row_to_list_type`, but works on mono types.
fn row_to_list_type(
    fields: &OrdMap<Name, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> mono::Type {
    let mut list_ty = mono::Type::empty();

    for (_field_name, field_ty) in fields.iter().rev() {
        // RecordField[field_ty]
        let record_field_args = vec![field_ty.clone()];
        let record_field_decl = poly_pgm.ty.get("RecordField").unwrap();
        mono_ty_decl(record_field_decl, &record_field_args, poly_pgm, mono_pgm);
        let record_field_ty = mono::Type::Named(mono::NamedType {
            name: Name::new_static("RecordField"),
            args: record_field_args,
        });

        // List[RecordField[field_ty], list_ty]
        let list_cons_args = vec![record_field_ty, list_ty];
        let list_cons_decl = poly_pgm.ty.get("List").unwrap();
        mono_ty_decl(list_cons_decl, &list_cons_args, poly_pgm, mono_pgm);
        list_ty = mono::Type::Named(mono::NamedType {
            name: Name::new_static("List"),
            args: list_cons_args,
        });
    }

    list_ty
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Types

/// Monomorphise a type-checking type.
fn mono_tc_ty(
    ty: &Ty,
    ty_map: &HashMap<Name, mono::Type>,
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
            let ty_decl = poly_pgm
                .ty
                .get(con.name())
                .unwrap_or_else(|| panic!("Unknown type constructor {}", con.name()));

            mono::Type::Named(mono::NamedType {
                name: mono_ty_decl(ty_decl, &[], poly_pgm, mono_pgm),
                args: vec![],
            })
        }

        Ty::RVar(var, _kind) => ty_map
            .get(&var)
            .unwrap_or_else(|| panic!("Unmapped rigid type variable {var}"))
            .clone(),

        Ty::App(con, args, _kind) => {
            let ty_decl = poly_pgm.ty.get(con.name()).unwrap();
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

        Ty::QVar(var, _kind) => {
            panic!("QVar {var} should not appear after type checking")
        }

        Ty::Fun {
            args,
            ret,
            exceptions,
        } => mono::Type::Fn(mono::FnType {
            args: match args {
                FunArgs::Positional { args } => mono::FunArgs::Positional(
                    args.iter()
                        .map(|arg| mono_tc_ty(arg, ty_map, poly_pgm, mono_pgm))
                        .collect(),
                ),
                FunArgs::Named { args, extension } => {
                    let mut all_args: OrdMap<Name, mono::Type> = args
                        .iter()
                        .map(|(arg_name, arg)| {
                            (
                                arg_name.clone(),
                                mono_tc_ty(arg, ty_map, poly_pgm, mono_pgm),
                            )
                        })
                        .collect();

                    if let Some(ty) = extension {
                        collect_record_rows(&ty, ty_map, &mut all_args, poly_pgm, mono_pgm);
                    }

                    mono::FunArgs::Named(all_args)
                }
            },
            ret: Box::new(mono_tc_ty(&ret, ty_map, poly_pgm, mono_pgm)),
            exn: Box::new(
                exceptions
                    .map(|ty| mono_tc_ty(&ty, ty_map, poly_pgm, mono_pgm))
                    .unwrap_or(mono::Type::empty()),
            ),
        }),

        Ty::Record {
            labels,
            extension,
            is_row: _,
        } => {
            let mut all_fields: OrdMap<Name, mono::Type> = Default::default();

            for (field, field_ty) in labels {
                let field_mono_ty = mono_tc_ty(&field_ty, ty_map, poly_pgm, mono_pgm);
                all_fields.insert(field, field_mono_ty);
            }

            if let Some(ty) = extension {
                collect_record_rows(&ty, ty_map, &mut all_fields, poly_pgm, mono_pgm);
            }

            mono::Type::Record { fields: all_fields }
        }

        Ty::Variant {
            labels,
            extension,
            is_row: _,
        } => {
            let mut all_alts: OrdMap<Name, mono::NamedType> = Default::default();

            for (id, ty) in labels.iter() {
                let ty = mono_tc_ty(ty, ty_map, poly_pgm, mono_pgm);
                match ty {
                    mono::Type::Named(named_ty) => {
                        let old = all_alts.insert(id.name().clone(), named_ty.clone());
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
                    Ty::RVar(var, _kind) => {
                        let ext = ty_map.get(var).unwrap();
                        match ext {
                            mono::Type::Variant { alts } => {
                                all_alts.extend(alts.iter().map(|(k, v)| (k.clone(), v.clone())));
                            }
                            _ => panic!(),
                        }
                    }

                    Ty::UVar(var) => {
                        assert!(var.link().is_none());
                    }

                    other => todo!("Weird row extension {other} ({other:?})"),
                }
            }

            mono::Type::Variant { alts: all_alts }
        }

        Ty::AssocTySelect {
            ty,
            assoc_ty,
            kind: _,
        } => {
            // The `ty` is a trait application like `Trait[Arg]`, not a regular type. Extract the
            // trait name and args directly, monomorphize only the args.
            let (trait_name, trait_args): (&Name, &[Ty]) = match ty.as_ref() {
                Ty::App(id, args, _kind) => (id.name(), args.as_slice()),
                Ty::Con(id, _kind) => (id.name(), &[]),
                _ => panic!("Expected trait constructor in AssocTySelect, got {:?}", ty),
            };
            let mono_args: Vec<mono::Type> = trait_args
                .iter()
                .map(|arg| mono_tc_ty(arg, ty_map, poly_pgm, mono_pgm))
                .collect();
            resolve_assoc_ty(trait_name, &mono_args, &assoc_ty, poly_pgm, mono_pgm)
        }
    }
}

fn mono_ast_ty(
    ty: &ast::Type,
    ty_map: &HashMap<Name, mono::Type>,
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
            is_row: _,
        } => {
            // For now we represent row and non-row records as the same type, but we may want to
            // pass this to `mono::Type::Record` if it helps with sanity checking in the use sites.
            mono::Type::Record {
                fields: collect_record_labels(fields, extension, ty_map, poly_pgm, mono_pgm),
            }
        }

        ast::Type::Variant {
            alts,
            extension,
            is_row: _,
        } => {
            // Same as the record case, we lose row and type distinction here.
            mono::Type::Variant {
                alts: collect_variant_labels(alts, extension, ty_map, poly_pgm, mono_pgm),
            }
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

        ast::Type::AssocTySelect { ty, assoc_ty } => {
            // Same as `Ty::AssocTySelect`.
            match &*ty.node {
                ast::Type::Named(ast::NamedType { name, args }) => {
                    let mono_args: Vec<mono::Type> = args
                        .iter()
                        .map(|arg| mono_ast_ty(&arg.node, ty_map, poly_pgm, mono_pgm))
                        .collect();
                    resolve_assoc_ty(name, &mono_args, assoc_ty, poly_pgm, mono_pgm)
                }
                ast::Type::Var(var) => {
                    panic!("Unexpected type variable {} in AssocTySelect", var);
                }
                _ => panic!("Expected named type in AssocTySelect, got {:?}", ty.node),
            }
        }
    }
}

/// Monomorphise a type declaration. Returns the name of the mono type.
fn mono_ty_decl(
    ty_decl: &ast::TypeDecl,
    args: &[mono::Type],
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> Name {
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
            value: ty_decl.value,
        },
    );

    // Maps type parameters of the type to type arguments.
    let ty_map: HashMap<Name, mono::Type> = ty_decl
        .type_params
        .iter()
        .map(|type_param| type_param.name.node.clone())
        .zip(args.iter().cloned())
        .collect();

    let rhs: Option<mono::TypeDeclRhs> = ty_decl.rhs.as_ref().map(|rhs| match rhs {
        ast::TypeDeclRhs::Sum { cons, extension } => {
            let mut mono_cons: Vec<mono::ConDecl> = cons
                .iter()
                .map(|con| mono_con(con, &ty_map, poly_pgm, mono_pgm))
                .collect();

            if let Some(ext) = extension {
                let ext_mono = resolve_extension_variant(&ext.node, &ty_map, poly_pgm, mono_pgm);
                for (alt_name, alt_ty) in ext_mono {
                    mono_cons.push(mono::ConDecl {
                        name: alt_name,
                        fields: if alt_ty.args.is_empty() {
                            mono::ConFields::Empty
                        } else {
                            mono::ConFields::Unnamed(alt_ty.args)
                        },
                    });
                }
            }

            mono::TypeDeclRhs::Sum(mono_cons)
        }

        ast::TypeDeclRhs::Product(fields) => {
            mono::TypeDeclRhs::Product(mono_fields(fields, &ty_map, poly_pgm, mono_pgm))
        }

        ast::TypeDeclRhs::Synonym(_) => {
            panic!("Type synonyms should be expanded before monomorphization")
        }
    });

    mono_pgm.ty.get_mut(&ty_decl.name).unwrap().insert(
        args.to_vec(),
        mono::TypeDecl {
            name: mono_ty_id.clone(),
            rhs,
            value: ty_decl.value,
        },
    );

    mono_ty_id
}

fn mono_con(
    con: &ast::ConDecl,
    ty_map: &HashMap<Name, mono::Type>,
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
    ty_map: &HashMap<Name, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> mono::ConFields {
    match fields {
        ast::ConFields::Empty => mono::ConFields::Empty,

        ast::ConFields::Named { fields, extension } => {
            let mut all_fields: OrdMap<Name, mono::Type> = fields
                .iter()
                .map(|(name, ty)| {
                    (
                        name.clone(),
                        mono_ast_ty(&ty.node, ty_map, poly_pgm, mono_pgm),
                    )
                })
                .collect();

            if let Some(ext) = extension {
                match mono_ast_ty(&ext.node, ty_map, poly_pgm, mono_pgm) {
                    mono::Type::Record { fields } => all_fields.extend(fields),
                    other @ (mono::Type::Named(_)
                    | mono::Type::Variant { .. }
                    | mono::Type::Fn(_)) => {
                        panic!("Weird row extension: {other} ({other:?})");
                    }
                }
            }

            mono::ConFields::Named(all_fields)
        }

        ast::ConFields::Unnamed { fields } => mono::ConFields::Unnamed(
            fields
                .iter()
                .map(|ty| mono_ast_ty(&ty.node, ty_map, poly_pgm, mono_pgm))
                .collect(),
        ),
    }
}

fn get_record_ty(ty: mono::Type, loc: &ast::Loc) -> OrdMap<Name, mono::Type> {
    match ty {
        mono::Type::Record { fields } => fields,

        other @ (mono::Type::Named(_) | mono::Type::Variant { .. } | mono::Type::Fn(_)) => {
            panic!(
                "{}: BUG: Record expression with non-record type: {}",
                loc_display(loc),
                other
            )
        }
    }
}

fn get_variant_ty(ty: mono::Type, loc: &ast::Loc) -> OrdMap<Name, mono::NamedType> {
    match ty {
        mono::Type::Variant { alts } => alts,

        other @ (mono::Type::Named(_) | mono::Type::Record { .. } | mono::Type::Fn(_)) => {
            panic!(
                "{}: BUG: Variant expression with non-record type: {}",
                loc_display(loc),
                other
            )
        }
    }
}

fn collect_record_labels(
    ast_fields: &[(Name, ast::Type)],
    extension: &Option<Box<ast::L<ast::Type>>>,
    ty_map: &HashMap<Name, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> OrdMap<Name, mono::Type> {
    let mut fields: OrdMap<Name, mono::Type> = Default::default();

    for (field_name, field_ty) in ast_fields.iter() {
        let old = fields.insert(
            field_name.clone(),
            mono_ast_ty(field_ty, ty_map, poly_pgm, mono_pgm),
        );
        if old.is_some() {
            panic!("BUG: Duplicate label in record");
        }
    }

    if let Some(ext) = extension {
        let extra_fields = resolve_extension_record(&ext.node, ty_map, poly_pgm, mono_pgm);
        for (extra_field_name, extra_field_ty) in extra_fields {
            let old = fields.insert(extra_field_name, extra_field_ty);
            if old.is_some() {
                panic!("BUG: Duplicate label in record");
            }
        }
    }

    fields
}

fn collect_variant_labels(
    ast_alts: &[ast::NamedType],
    extension: &Option<Box<ast::L<ast::Type>>>,
    ty_map: &HashMap<Name, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> OrdMap<Name, mono::NamedType> {
    let mut alts: OrdMap<Name, mono::NamedType> = Default::default();

    // Note: technically duplicate labels in variants are never a problem and we should be able to
    // relax the error checking below.
    //
    // Currently we use a `Map<ConId, Ty>` for the variant types, which prevents having e.g.
    // `Option[U32]` and `Option[U64]` in the same variant type, as they would have the same type
    // constructor id. (`Option`)
    //
    // I can't remember/think of a reason why we have this restriction. We can always add more
    // labels to a variant, it never becomes invalid/unsound/etc. so we should eventually remove
    // this restriction. (maybe in the self-hosted compiler)
    //
    // The checks below are different in `collect_record_labels` above. Because we don't allow
    // record extensions we never add fields to a record. E.g. you can't write a function with a
    // type like `Fn(arg: (..r)) (x: U32, ..r)`, but you can write `Fn(arg: [..r]) [A, ..r]`.

    for ast::NamedType { name, args } in ast_alts.iter() {
        let alt_ty = mono::NamedType {
            name: name.clone(),
            args: args
                .iter()
                .map(|ty| mono_ast_ty(&ty.node, ty_map, poly_pgm, mono_pgm))
                .collect(),
        };
        let old = alts.insert(name.clone(), alt_ty.clone());
        if let Some(old) = old
            && old != alt_ty
        {
            panic!("Type error: duplicate label in variant");
        }
    }

    if let Some(ext) = extension {
        let extra_alts = resolve_extension_variant(&ext.node, ty_map, poly_pgm, mono_pgm);
        for (extra_alt_label, extra_alt_ty) in extra_alts {
            let old = alts.insert(extra_alt_label, extra_alt_ty.clone());
            if let Some(old) = old.as_ref()
                && old != &extra_alt_ty
            {
                panic!("Type error: duplicate label in variant");
            }
        }
    }

    alts
}

fn resolve_extension_record(
    ext: &ast::Type,
    ty_map: &HashMap<Name, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> OrdMap<Name, mono::Type> {
    match ext {
        ast::Type::Var(id) => match ty_map.get(id) {
            Some(mono::Type::Record { fields }) => fields.clone(),
            Some(other) => panic!("BUG: Record extension is not a record: {other:?}"),
            None => panic!(
                "BUG: Record extension var not in ty map: {id}\n\
                Ty map = {ty_map:#?}"
            ),
        },
        ast::Type::Record {
            fields,
            extension,
            is_row,
        } => {
            assert!(*is_row);
            collect_record_labels(fields, extension, ty_map, poly_pgm, mono_pgm)
        }
        other => panic!("BUG: Record extension is not a var or record: {other:?}"),
    }
}

fn resolve_extension_variant(
    ext: &ast::Type,
    ty_map: &HashMap<Name, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> OrdMap<Name, mono::NamedType> {
    match ext {
        ast::Type::Var(id) => match ty_map.get(id) {
            Some(mono::Type::Variant { alts }) => alts.clone(),
            Some(other) => panic!("BUG: Variant extension is not a variant: {other:?}"),
            None => panic!(
                "BUG: Variant extension var not in ty map: {id}\n\
                Ty map = {ty_map:#?}"
            ),
        },
        ast::Type::Variant {
            alts,
            extension,
            is_row,
        } => {
            assert!(*is_row);
            collect_variant_labels(alts, extension, ty_map, poly_pgm, mono_pgm)
        }
        other => panic!("BUG: Variant extension is not a var or variant: {other:?}"),
    }
}

fn collect_record_rows(
    ext_ty: &Ty,
    ty_map: &HashMap<Name, mono::Type>,
    rows: &mut OrdMap<Name, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) {
    // We can't check this yet as we don't keep track of `ast::Type::AssocTySelect` kinds and return
    // `*` for all assoc types in `ast::Type::kind` and also the `Ty::kind`.
    // assert!(matches!(ext_ty.kind(), Kind::Row(_)));
    match ext_ty {
        Ty::AssocTySelect {
            ty,
            assoc_ty,
            kind: _,
        } => {
            let (trait_name, trait_args): (&Name, &[Ty]) = match ty.as_ref() {
                Ty::App(id, args, _kind) => (id.name(), args.as_slice()),
                Ty::Con(id, _kind) => (id.name(), &[]),
                _ => panic!("Expected trait constructor in AssocTySelect, got {:?}", ty),
            };
            let mono_args: Vec<mono::Type> = trait_args
                .iter()
                .map(|arg| mono_tc_ty(arg, ty_map, poly_pgm, mono_pgm))
                .collect();
            let mono_ext_ty =
                resolve_assoc_ty(trait_name, &mono_args, assoc_ty, poly_pgm, mono_pgm);
            match mono_ext_ty {
                mono::Type::Record { fields } => rows.extend(fields),
                mono::Type::Named(_) | mono::Type::Variant { .. } | mono::Type::Fn(_) => {
                    panic!("Weird row extension: {mono_ext_ty} ({mono_ext_ty:?})")
                }
            }
        }

        Ty::RVar(var, _kind) => {
            let ext = ty_map.get(var).unwrap();
            match ext {
                mono::Type::Record { fields } => {
                    rows.extend(fields.iter().map(|(k, v)| (k.clone(), v.clone())));
                }
                _ => panic!(),
            }
        }

        Ty::UVar(var) => {
            assert!(var.link().is_none());
        }

        other => panic!("Weird row extension: {other} ({other:?})"),
    }
}

fn synthesize_row_to_list(ty_args: &[mono::Type], poly_pgm: &PolyPgm, mono_pgm: &mut MonoPgm) {
    if mono_pgm
        .associated
        .get("RecRowToList")
        .and_then(|m| m.get("rowToList"))
        .and_then(|m| m.get(ty_args))
        .is_some()
    {
        return;
    }

    // row, exn (implicit)
    assert_eq!(ty_args.len(), 2);

    let fields = match &ty_args[0] {
        mono::Type::Record { fields } => fields.clone(),
        other => panic!("RecRowToList type arg is not a record: {other:?}"),
    };

    // The method parameter type is (..recRow) which is a record with the row's fields.
    let rec_ty = mono::Type::Record {
        fields: fields.clone(),
    };

    let list_ty = row_to_list_type(&fields, poly_pgm, mono_pgm);

    // Build body that returns `Option[List[...]]`.

    // Return type is `Option[list_ty]`.
    let option_list_ty = mono::Type::Named(mono::NamedType {
        name: Name::new_static("Option"),
        args: vec![list_ty.clone()],
    });

    let body_expr = if fields.is_empty() {
        // Option.None
        ast::L::new_dummy(mono::Expr::ConSel(mono::Con {
            ty_id: Name::new_static("Option"),
            con: Some(Name::new_static("None")),
            ty_args: vec![list_ty.clone()],
            ty: option_list_ty.clone(),
        }))
    } else {
        // Start with `Option.None` for the innermost tail.
        let mut inner_expr = ast::L::new_dummy(mono::Expr::ConSel(mono::Con {
            ty_id: Name::new_static("Option"),
            con: Some(Name::new_static("None")),
            ty_args: vec![mono::Type::empty()],
            ty: mono::Type::Named(mono::NamedType {
                name: Name::new_static("Option"),
                args: vec![mono::Type::empty()],
            }),
        }));

        let mut tail_ty = mono::Type::empty();

        let fields_vec: Vec<(&Name, &mono::Type)> = fields.iter().collect();

        // Wrap each field in `RecordField` and `List`, from last to first.
        for (i, (field_name, field_ty)) in fields_vec.iter().copied().enumerate().rev() {
            // rec.fieldName
            let field_sel = ast::L::new_dummy(mono::Expr::FieldSel(mono::FieldSelExpr {
                object: Box::new(ast::L::new_dummy(mono::Expr::LocalVar(
                    Name::new_static("rec"),
                    rec_ty.clone(),
                ))),
                field: field_name.clone(),
                ty: field_ty.clone(),
            }));

            // RecordField[field_ty]
            let record_field_con_ty = mono::Type::Named(mono::NamedType {
                name: Name::new_static("RecordField"),
                args: vec![field_ty.clone()],
            });
            let record_field_fn_ty = mono::Type::Fn(mono::FnType {
                args: mono::FunArgs::Named(
                    [
                        (Name::new_static("label"), mono::Type::str()),
                        (Name::new_static("value_"), field_ty.clone()),
                    ]
                    .into_iter()
                    .collect(),
                ),
                ret: Box::new(record_field_con_ty.clone()),
                exn: Box::new(mono::Type::empty()),
            });
            let record_field_expr = ast::L::new_dummy(mono::Expr::Call(mono::CallExpr {
                fun: Box::new(ast::L::new_dummy(mono::Expr::ConSel(mono::Con {
                    ty_id: Name::new_static("RecordField"),
                    con: None,
                    ty_args: vec![field_ty.clone()],
                    ty: record_field_fn_ty,
                }))),
                args: vec![
                    mono::CallArg {
                        name: Some(Name::new_static("label")),
                        expr: ast::L::new_dummy(mono::Expr::Str(field_name.to_string())),
                    },
                    mono::CallArg {
                        name: Some(Name::new_static("value_")),
                        expr: field_sel,
                    },
                ],
                splice: None,
                ty: record_field_con_ty.clone(),
            }));

            // Option[tail_ty], the type of the `tail` field
            let option_tail_ty = mono::Type::Named(mono::NamedType {
                name: Name::new_static("Option"),
                args: vec![tail_ty.clone()],
            });

            // List[RecordField[field_ty], tail_ty]
            let list_cons_ty = mono::Type::Named(mono::NamedType {
                name: Name::new_static("List"),
                args: vec![record_field_con_ty.clone(), tail_ty.clone()],
            });
            let list_cons_fn_ty = mono::Type::Fn(mono::FnType {
                args: mono::FunArgs::Named(
                    [
                        (Name::new_static("head"), record_field_con_ty),
                        (Name::new_static("tail"), option_tail_ty),
                    ]
                    .into_iter()
                    .collect(),
                ),
                ret: Box::new(list_cons_ty.clone()),
                exn: Box::new(mono::Type::empty()),
            });
            inner_expr = ast::L::new_dummy(mono::Expr::Call(mono::CallExpr {
                fun: Box::new(ast::L::new_dummy(mono::Expr::ConSel(mono::Con {
                    ty_id: Name::new_static("List"),
                    con: None,
                    ty_args: vec![
                        mono::Type::Named(mono::NamedType {
                            name: Name::new_static("RecordField"),
                            args: vec![field_ty.clone()],
                        }),
                        tail_ty,
                    ],
                    ty: list_cons_fn_ty,
                }))),
                args: vec![
                    mono::CallArg {
                        name: Some(Name::new_static("head")),
                        expr: record_field_expr,
                    },
                    mono::CallArg {
                        name: Some(Name::new_static("tail")),
                        expr: inner_expr,
                    },
                ],
                splice: None,
                ty: list_cons_ty.clone(),
            }));

            // If not the outermost element, wrap in `Option.Some` for the next iteration.
            if i > 0 {
                let option_cons_ty = mono::Type::Named(mono::NamedType {
                    name: Name::new_static("Option"),
                    args: vec![list_cons_ty.clone()],
                });
                let some_fn_ty = mono::Type::Fn(mono::FnType {
                    args: mono::FunArgs::Positional(vec![list_cons_ty.clone()]),
                    ret: Box::new(option_cons_ty.clone()),
                    exn: Box::new(mono::Type::empty()),
                });
                inner_expr = ast::L::new_dummy(mono::Expr::Call(mono::CallExpr {
                    fun: Box::new(ast::L::new_dummy(mono::Expr::ConSel(mono::Con {
                        ty_id: Name::new_static("Option"),
                        con: Some(Name::new_static("Some")),
                        ty_args: vec![list_cons_ty.clone()],
                        ty: some_fn_ty,
                    }))),
                    args: vec![mono::CallArg {
                        name: None,
                        expr: inner_expr,
                    }],
                    splice: None,
                    ty: option_cons_ty,
                }));
            }
            tail_ty = list_cons_ty;
        }

        // Wrap the outermost List in Option.Some.
        let some_fn_ty = mono::Type::Fn(mono::FnType {
            args: mono::FunArgs::Positional(vec![list_ty.clone()]),
            ret: Box::new(option_list_ty.clone()),
            exn: Box::new(mono::Type::empty()),
        });
        ast::L::new_dummy(mono::Expr::Call(mono::CallExpr {
            fun: Box::new(ast::L::new_dummy(mono::Expr::ConSel(mono::Con {
                ty_id: Name::new_static("Option"),
                con: Some(Name::new_static("Some")),
                ty_args: vec![list_ty.clone()],
                ty: some_fn_ty,
            }))),
            args: vec![mono::CallArg {
                name: None,
                expr: inner_expr,
            }],
            splice: None,
            ty: option_list_ty.clone(),
        }))
    };

    let fun_decl = mono::FunDecl {
        parent_ty: Some(ast::L::new_dummy(Name::new_static("RecRowToList"))),
        name: ast::L::new_dummy(Name::new_static("rowToList")),
        sig: mono::FunSig {
            params: vec![(Name::new_static("rec"), ast::L::new_dummy(rec_ty))],
            return_ty: Some(ast::L::new_dummy(option_list_ty)),
            exceptions: None,
        },
        body: Some(vec![ast::L::new_dummy(mono::Stmt::Expr(body_expr.node))]),
    };

    mono_pgm
        .associated
        .entry(Name::new_static("RecRowToList"))
        .or_default()
        .entry(Name::new_static("rowToList"))
        .or_default()
        .insert(ty_args.to_vec(), fun_decl);
}
