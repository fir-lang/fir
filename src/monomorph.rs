/*!
This module implements some kind of monomorphisation.

We have two goals with this pass:

- Avoid storing numbers as boxed in arrays.
  (which are used in: vectors, strings, ...)

- Avoid boxing numbers. (I32, I8, ...)

The idea is that because we don't have garbage collection in the interpreter, we should avoid
allocations when easily possible (such as for integers), and shouldn't have to box all array
elements and allocate arrays larger than necessary (e.g. I64 arrays instead of I8 for the unicode
encodings in string types).

In the future we may extend this to support unboxing boxed values to multiple scalar values.

The monomorphised functions and types will have suffixes instead of type parameters indicating
monomorphised type parameters. For example:

```ignore
type Vec[T]:
    data: Array[T]
    len: U32

fn print[T1: ToStr, T2: ToStr](a: T1, b: T2) = ...
```

can be monomorphised to these variants:

```ignore
type Vec#I8:
    data: Array#I8
    len: U32

type Vec#Ptr:
    data: Array#Ptr
    len: U32

fn print#I8#Ptr(a: I8, b: Ptr) = ...
fn print#I64#I64(a: I64, b: I64) = ...
```

This pass only looks at `Instantiation` nodes to monomorphise, we should be introduced by the
previous pass.

The resulting program won't have any `Instantiation` nodes.

# Monomorphising patterns

If a type is only mentioned by a pattern but by no terms, then it can never match, so we don't have
to collect and monomorphise types in patterns.
*/

use crate::ast;
use crate::collections::Map;
use crate::interpolation::StringPart;
use crate::type_checker::{Id, Ty, TyArgs};

use smol_str::SmolStr;

/*
Implementation plan:

- Convert the program into a graph to be able to easily look up symbols.

- The monomorphised program will also be a graph that we serialize afterwards.

- Some kind of "item" type as pointers to these graph nodes.

- Start from main to monomorphise. Every reference to a definition gets added to the graph.

    - If the reference is from an instantiation: the monomorphised version of the target is added
      to the graph, and the instantiation is converted into a `Var` (or `ConstrSelect` etc.) to the
      monomorphised definition.

    - If the reference is not from an instantiation: just add the definition to the graph and call it.

    This also removes dead code.
*/

/// Type checked program, converted into a graph.
#[derive(Debug, Default)]
struct PgmGraph {
    top: Map<Id, ast::FunDecl>,
    associated: Map<Id, Map<Id, ast::FunDecl>>,
    ty: Map<Id, ast::TypeDecl>,
}

// TODO: This drops traits, we should copy missing methods with default implementations before
// converting to the graph.
fn pgm_to_graph(pgm: Vec<ast::TopDecl>) -> PgmGraph {
    let mut top: Map<Id, ast::FunDecl> = Default::default();
    let mut associated: Map<Id, Map<Id, ast::FunDecl>> = Default::default();
    let mut ty: Map<Id, ast::TypeDecl> = Default::default();

    // NB. Assertions below are errors that the type checker should catch.
    for decl in pgm {
        match decl {
            ast::TopDecl::Type(ty_decl) => {
                let old = ty.insert(ty_decl.node.name.clone(), ty_decl.node);
                assert!(old.is_none(), "BUG: Type declared multiple times");
            }

            ast::TopDecl::Fun(fun_decl) => {
                let old = top.insert(fun_decl.node.sig.name.node.clone(), fun_decl.node);
                assert!(
                    old.is_none(),
                    "BUG: Top-level function declared multiple times"
                );
            }

            ast::TopDecl::Impl(impl_decl) => {
                let ty_id = match &impl_decl.node.ty.node {
                    ast::Type::Named(ast::NamedType { name, args: _ }) => name.clone(),
                    _ => panic!(), // should be checked by type checker
                };

                for item in impl_decl.node.items {
                    match item.node {
                        ast::ImplDeclItem::AssocTy(_) => continue,
                        ast::ImplDeclItem::Fun(fun_decl) => {
                            let old = associated
                                .entry(ty_id.clone())
                                .or_default()
                                .insert(fun_decl.sig.name.node.clone(), fun_decl);
                            assert!(
                                old.is_none(),
                                "BUG: Associated function defined multiple times"
                            );
                        }
                    }
                }
            }

            ast::TopDecl::Import(_) | ast::TopDecl::Trait(_) => continue,
        }
    }

    PgmGraph {
        top,
        associated,
        ty,
    }
}

fn graph_to_pgm(graph: PgmGraph) -> Vec<ast::TopDecl> {
    let mut pgm: Vec<ast::TopDecl> = Vec::with_capacity(graph.top.len() + graph.ty.len());

    let PgmGraph {
        top,
        associated,
        ty,
    } = graph;

    for (_, ty_decl) in ty {
        pgm.push(ast::TopDecl::Type(ast::L {
            loc: ast::Loc::dummy(),
            node: ty_decl,
        }));
    }

    for (_, top_decl) in top {
        pgm.push(ast::TopDecl::Fun(ast::L {
            loc: ast::Loc::dummy(),
            node: top_decl,
        }));
    }

    for (ty_id, funs) in associated {
        pgm.push(ast::TopDecl::Impl(ast::L {
            loc: ast::Loc::dummy(),
            node: ast::ImplDecl {
                context: vec![],
                trait_: None,
                ty: ast::L {
                    loc: ast::Loc::dummy(),
                    node: ast::Type::Named(ast::NamedType {
                        name: ty_id,
                        args: vec![],
                    }),
                },
                items: funs
                    .into_values()
                    .map(|fun_decl| ast::L {
                        loc: ast::Loc::dummy(),
                        node: ast::ImplDeclItem::Fun(fun_decl),
                    })
                    .collect(),
            },
        }))
    }

    pgm
}

// Testing.
pub fn monomorphise(pgm: &[ast::L<ast::TopDecl>]) -> Vec<ast::L<ast::TopDecl>> {
    let poly_pgm = pgm_to_graph(pgm.iter().map(|decl| decl.node.clone()).collect());
    let mut mono_pgm = PgmGraph::default();

    let main = poly_pgm.top.get("main").unwrap();
    mono_top_decl(main, &[], &poly_pgm, &mut mono_pgm);

    let mono_pgm = graph_to_pgm(mono_pgm);
    let mut buffer = String::new();
    for item in &mono_pgm {
        item.print(&mut buffer, 0);
        buffer.push('\n');
    }
    println!("{}", buffer);

    mono_pgm
        .into_iter()
        .map(|decl| ast::L {
            loc: ast::Loc::dummy(),
            node: decl,
        })
        .collect()
}

fn mono_top_decl(
    top_decl: &ast::FunDecl,
    ty_args: &[ast::Type],
    poly_pgm: &PgmGraph,
    mono_pgm: &mut PgmGraph,
) -> Id {
    assert_eq!(top_decl.sig.type_params.len(), ty_args.len());

    let mono_fn_id = mono_id(&top_decl.sig.name.node, ty_args);

    // Check if we've already monomorphised this function.
    if mono_pgm.top.contains_key(&mono_fn_id) {
        return mono_fn_id;
    }

    // Add current function to mono_pgm without a body to avoid looping.
    let ty_map: Map<Id, ast::Type> = top_decl
        .sig
        .type_params
        .iter()
        .map(|ty_param| ty_param.node.0.node.clone())
        .zip(ty_args.iter().cloned())
        .collect();

    let params: Vec<(Id, ast::L<ast::Type>)> = top_decl
        .sig
        .params
        .iter()
        .map(|(param_name, param_ty)| {
            (
                param_name.clone(),
                param_ty.map_as_ref(|ty| mono_ty(ty, &ty_map, poly_pgm, mono_pgm)),
            )
        })
        .collect();

    let return_ty: Option<ast::L<ast::Type>> = top_decl
        .sig
        .return_ty
        .as_ref()
        .map(|ty| ty.map_as_ref(|ty| mono_ty(ty, &ty_map, poly_pgm, mono_pgm)));

    mono_pgm.top.insert(
        mono_fn_id.clone(),
        ast::FunDecl {
            sig: ast::FunSig {
                name: top_decl.sig.name.set_node(mono_fn_id.clone()),
                type_params: vec![],
                self_: top_decl.sig.self_,
                params,
                return_ty,
            },
            body: None,
        },
    );

    // Monomorphise function body.
    let body = match &top_decl.body {
        Some(body) => body,
        None => return mono_fn_id,
    };

    let mono_body = body.map_as_ref(|lstmts| mono_lstmts(lstmts, &ty_map, poly_pgm, mono_pgm));

    mono_pgm.top.get_mut(&mono_fn_id).unwrap().body = Some(mono_body);

    mono_fn_id
}

fn mono_stmt(
    stmt: &ast::Stmt,
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PgmGraph,
    mono_pgm: &mut PgmGraph,
) -> ast::Stmt {
    match stmt {
        ast::Stmt::Let(ast::LetStmt { lhs, ty, rhs }) => ast::Stmt::Let(ast::LetStmt {
            lhs: lhs.clone(),
            ty: ty
                .as_ref()
                .map(|ty| ty.map_as_ref(|ty| mono_ty(ty, ty_map, poly_pgm, mono_pgm))),
            rhs: rhs.map_as_ref(|expr| mono_expr(expr, ty_map, poly_pgm, mono_pgm)),
        }),

        ast::Stmt::Assign(ast::AssignStmt { lhs, rhs, op }) => ast::Stmt::Assign(ast::AssignStmt {
            lhs: lhs.map_as_ref(|expr| mono_expr(expr, ty_map, poly_pgm, mono_pgm)),
            rhs: rhs.map_as_ref(|expr| mono_expr(expr, ty_map, poly_pgm, mono_pgm)),
            op: *op,
        }),

        ast::Stmt::Expr(expr) => {
            ast::Stmt::Expr(expr.map_as_ref(|expr| mono_expr(expr, ty_map, poly_pgm, mono_pgm)))
        }

        ast::Stmt::For(ast::ForStmt {
            var,
            ty,
            expr,
            body,
        }) => ast::Stmt::For(ast::ForStmt {
            var: var.clone(),
            ty: ty
                .as_ref()
                .map(|ty| mono_ty(ty, ty_map, poly_pgm, mono_pgm)),
            expr: expr.map_as_ref(|expr| mono_expr(expr, ty_map, poly_pgm, mono_pgm)),
            body: mono_lstmts(body, ty_map, poly_pgm, mono_pgm),
        }),

        ast::Stmt::While(ast::WhileStmt { cond, body }) => ast::Stmt::While(ast::WhileStmt {
            cond: cond.map_as_ref(|expr| mono_expr(expr, ty_map, poly_pgm, mono_pgm)),
            body: mono_lstmts(body, ty_map, poly_pgm, mono_pgm),
        }),
    }
}

fn mono_expr(
    expr: &ast::Expr,
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PgmGraph,
    mono_pgm: &mut PgmGraph,
) -> ast::Expr {
    match expr {
        ast::Expr::Instantiation(path, ty_args) => {
            let mono_ty_args: Vec<ast::Type> = ty_args
                .iter()
                .map(|ty_arg| mono_ty(&ty_to_ast(ty_arg, ty_map), ty_map, poly_pgm, mono_pgm))
                .collect();

            match path {
                ast::Path::TopLevel { fun_id } => {
                    if let Some(fun_decl) = poly_pgm.top.get(fun_id) {
                        let mono_fun_id =
                            mono_top_decl(fun_decl, &mono_ty_args, poly_pgm, mono_pgm);
                        return ast::Expr::Var(mono_fun_id);
                    }

                    if let Some(ty_decl) = poly_pgm.ty.get(fun_id) {
                        let mono_ty_id = mono_ty_decl(ty_decl, &mono_ty_args, poly_pgm, mono_pgm);
                        return ast::Expr::UpperVar(mono_ty_id);
                    }

                    panic!()
                }

                ast::Path::Constructor { ty_id, constr_id } => {
                    let ty_decl = poly_pgm.ty.get(ty_id).unwrap();
                    let mono_ty_id = mono_ty_decl(ty_decl, &mono_ty_args, poly_pgm, mono_pgm);
                    ast::Expr::ConstrSelect(ast::ConstrSelectExpr {
                        ty: mono_ty_id,
                        constr: constr_id.clone(),
                    })
                }

                ast::Path::AssociatedFn { ty_id, fun_id } => {
                    let ty_decl = poly_pgm.ty.get(ty_id).unwrap();
                    let ty_num_type_params = ty_decl.type_params.len();

                    let mono_ty_id = mono_ty_decl(
                        ty_decl,
                        &mono_ty_args[0..ty_num_type_params],
                        poly_pgm,
                        mono_pgm,
                    );

                    let fun_decl = poly_pgm.associated.get(ty_id).unwrap().get(fun_id).unwrap();

                    let ty_map: Map<Id, ast::Type> = ty_decl
                        .type_params
                        .iter()
                        .cloned()
                        .zip(mono_ty_args.iter().cloned())
                        .collect();

                    let mono_fun_id = mono_assoc_fn(
                        &mono_ty_id,
                        fun_decl,
                        &ty_map,
                        &mono_ty_args[ty_num_type_params..],
                        poly_pgm,
                        mono_pgm,
                    );

                    ast::Expr::FieldSelect(ast::FieldSelectExpr {
                        object: Box::new(ast::L {
                            loc: ast::Loc::dummy(),
                            node: ast::Expr::Var(mono_ty_id),
                        }),
                        field: mono_fun_id,
                    })
                }

                ast::Path::Method {
                    receiver,
                    receiver_ty,
                    method_id,
                } => {
                    let poly_receiver_ty = ty_to_ast(receiver_ty, ty_map);

                    let mono_receiver_ty = mono_ty(&poly_receiver_ty, ty_map, poly_pgm, mono_pgm);

                    let mono_receiver_ty_id = match mono_receiver_ty {
                        ast::Type::Named(ast::NamedType { name, args }) => {
                            assert!(args.is_empty());
                            name
                        }
                        ast::Type::Record(_) => panic!(),
                    };

                    // Monomorphise associated function/method.
                    match &poly_receiver_ty {
                        ast::Type::Named(ast::NamedType { name, args }) => {
                            let ty_con = poly_pgm.ty.get(name).unwrap();
                            assert_eq!(ty_con.type_params.len(), args.len());

                            let fun = poly_pgm
                                .associated
                                .get(name)
                                .unwrap()
                                .get(method_id)
                                .unwrap();

                            let mut assoc_fn_ty_map = ty_map.clone();
                            for (ty_param, ty_arg) in ty_con.type_params.iter().zip(args.iter()) {
                                assoc_fn_ty_map
                                    .insert(ty_param.clone(), ty_arg.node.1.node.clone());
                            }

                            mono_assoc_fn(
                                &mono_receiver_ty_id,
                                fun,
                                &assoc_fn_ty_map,
                                &mono_ty_args,
                                poly_pgm,
                                mono_pgm,
                            );
                        }
                        ast::Type::Record(_) => panic!(),
                    }

                    let mono_receiver = mono_expr(receiver, ty_map, poly_pgm, mono_pgm);
                    ast::Expr::FieldSelect(ast::FieldSelectExpr {
                        object: Box::new(ast::L {
                            loc: ast::Loc::dummy(), // TODO
                            node: mono_receiver,
                        }),
                        field: method_id.clone(),
                    })
                }
            }
        }

        ast::Expr::Var(var) => ast::Expr::Var(match poly_pgm.top.get(var) {
            Some(fun_decl) => mono_top_decl(fun_decl, &[], poly_pgm, mono_pgm),
            None => var.clone(),
        }),

        ast::Expr::ConstrSelect(ast::ConstrSelectExpr { ty, constr }) => {
            let ty_decl = poly_pgm.ty.get(ty).unwrap();
            mono_ty_decl(ty_decl, &[], poly_pgm, mono_pgm);
            ast::Expr::ConstrSelect(ast::ConstrSelectExpr {
                ty: ty.clone(),
                constr: constr.clone(),
            })
        }

        ast::Expr::Int(int) => {
            let ty_decl_id = match int {
                ast::IntExpr::I8(_) => "I8",
                ast::IntExpr::U8(_) => "U8",
                ast::IntExpr::I32(_) => "I32",
                ast::IntExpr::U32(_) => "U32",
            };
            let ty_decl = poly_pgm.ty.get(ty_decl_id).unwrap();
            mono_ty_decl(ty_decl, &[], poly_pgm, mono_pgm);
            ast::Expr::Int(int.clone())
        }

        ast::Expr::Char(char) => {
            let ty_decl = poly_pgm.ty.get("Char").unwrap();
            mono_ty_decl(ty_decl, &[], poly_pgm, mono_pgm);
            ast::Expr::Char(*char)
        }

        ast::Expr::UpperVar(_) | ast::Expr::Self_ => expr.clone(),

        ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field }) => {
            // TODO: When the field is a method we should monomorphise here it to add it to the mono pgm.
            ast::Expr::FieldSelect(ast::FieldSelectExpr {
                object: mono_bl_expr(object, ty_map, poly_pgm, mono_pgm),
                field: field.clone(),
            })
        }

        ast::Expr::Call(ast::CallExpr { fun, args }) => ast::Expr::Call(ast::CallExpr {
            fun: mono_bl_expr(fun, ty_map, poly_pgm, mono_pgm),
            args: args
                .iter()
                .map(|ast::CallArg { name, expr }| ast::CallArg {
                    name: name.clone(),
                    expr: mono_l_expr(expr, ty_map, poly_pgm, mono_pgm),
                })
                .collect(),
        }),

        ast::Expr::Range(ast::RangeExpr {
            from,
            to,
            inclusive,
        }) => ast::Expr::Range(ast::RangeExpr {
            from: mono_bl_expr(from, ty_map, poly_pgm, mono_pgm),
            to: mono_bl_expr(to, ty_map, poly_pgm, mono_pgm),
            inclusive: *inclusive,
        }),

        ast::Expr::String(parts) => ast::Expr::String(
            parts
                .iter()
                .map(|part| match part {
                    StringPart::Str(str) => StringPart::Str(str.clone()),
                    StringPart::Expr(expr) => {
                        StringPart::Expr(mono_l_expr(expr, ty_map, poly_pgm, mono_pgm))
                    }
                })
                .collect(),
        ),

        ast::Expr::BinOp(ast::BinOpExpr { left, right, op }) => ast::Expr::BinOp(ast::BinOpExpr {
            left: mono_bl_expr(left, ty_map, poly_pgm, mono_pgm),
            right: mono_bl_expr(right, ty_map, poly_pgm, mono_pgm),
            op: op.clone(),
        }),

        ast::Expr::UnOp(ast::UnOpExpr { op, expr }) => ast::Expr::UnOp(ast::UnOpExpr {
            op: op.clone(),
            expr: mono_bl_expr(expr, ty_map, poly_pgm, mono_pgm),
        }),

        ast::Expr::ArrayIndex(_) => todo!(),

        ast::Expr::Record(_) => todo!(),

        ast::Expr::Return(expr) => {
            ast::Expr::Return(mono_bl_expr(expr, ty_map, poly_pgm, mono_pgm))
        }

        ast::Expr::Match(ast::MatchExpr { scrutinee, alts }) => ast::Expr::Match(ast::MatchExpr {
            scrutinee: mono_bl_expr(scrutinee, ty_map, poly_pgm, mono_pgm),
            alts: alts
                .iter()
                .map(
                    |ast::Alt {
                         pattern,
                         guard,
                         rhs,
                     }| ast::Alt {
                        pattern: pattern.clone(),
                        guard: guard
                            .as_ref()
                            .map(|expr| mono_l_expr(expr, ty_map, poly_pgm, mono_pgm)),
                        rhs: mono_lstmts(rhs, ty_map, poly_pgm, mono_pgm),
                    },
                )
                .collect(),
        }),

        ast::Expr::If(ast::IfExpr {
            branches,
            else_branch,
        }) => ast::Expr::If(ast::IfExpr {
            branches: branches
                .iter()
                .map(|(expr, stmts)| {
                    (
                        mono_l_expr(expr, ty_map, poly_pgm, mono_pgm),
                        mono_lstmts(stmts, ty_map, poly_pgm, mono_pgm),
                    )
                })
                .collect(),
            else_branch: else_branch
                .as_ref()
                .map(|stmts| mono_lstmts(stmts, ty_map, poly_pgm, mono_pgm)),
        }),
    }
}

fn mono_lstmts(
    lstmts: &[ast::L<ast::Stmt>],
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PgmGraph,
    mono_pgm: &mut PgmGraph,
) -> Vec<ast::L<ast::Stmt>> {
    lstmts
        .iter()
        .map(|lstmt| lstmt.map_as_ref(|stmt| mono_stmt(stmt, ty_map, poly_pgm, mono_pgm)))
        .collect()
}

fn mono_bl_expr(
    expr: &ast::L<ast::Expr>,
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PgmGraph,
    mono_pgm: &mut PgmGraph,
) -> Box<ast::L<ast::Expr>> {
    Box::new(expr.map_as_ref(|expr| mono_expr(expr, ty_map, poly_pgm, mono_pgm)))
}

fn mono_l_expr(
    expr: &ast::L<ast::Expr>,
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PgmGraph,
    mono_pgm: &mut PgmGraph,
) -> ast::L<ast::Expr> {
    expr.map_as_ref(|expr| mono_expr(expr, ty_map, poly_pgm, mono_pgm))
}

/// Monomorphise an associated function or method.
///
/// `ty_map` maps type parameters of the type to mono types.
///
/// `ty_args` should not include the type's arguments, it should only have the function's type
/// arguments.
fn mono_assoc_fn(
    mono_ty_id: &Id,
    fun: &ast::FunDecl,
    ty_map: &Map<Id, ast::Type>,
    ty_args: &[ast::Type],
    poly_pgm: &PgmGraph,
    mono_pgm: &mut PgmGraph,
) -> Id {
    let mono_fn_id = mono_id(&fun.sig.name.node, ty_args);

    if mono_pgm
        .associated
        .entry(mono_ty_id.clone())
        .or_default()
        .contains_key(&mono_fn_id)
    {
        return mono_fn_id;
    }

    let mut ty_map = ty_map.clone();
    let fun_ty_params = &fun.sig.type_params[fun.sig.type_params.len() - ty_args.len()..];
    for (ty_param, mono_ty) in fun_ty_params
        .iter()
        .map(|ty_param| ty_param.node.0.node.clone())
        .zip(ty_args.iter().cloned())
    {
        ty_map.insert(ty_param, mono_ty);
    }

    if fun.sig.self_ {
        ty_map.insert(
            SmolStr::new("self"),
            ast::Type::Named(ast::NamedType {
                name: mono_ty_id.clone(),
                args: vec![],
            }),
        );
    }

    let params: Vec<(Id, ast::L<ast::Type>)> = fun
        .sig
        .params
        .iter()
        .map(|(param_name, param_ty)| {
            (
                param_name.clone(),
                param_ty.map_as_ref(|ty| mono_ty(ty, &ty_map, poly_pgm, mono_pgm)),
            )
        })
        .collect();

    let return_ty: Option<ast::L<ast::Type>> = fun
        .sig
        .return_ty
        .as_ref()
        .map(|ty| ty.map_as_ref(|ty| mono_ty(ty, &ty_map, poly_pgm, mono_pgm)));

    mono_pgm
        .associated
        .entry(mono_ty_id.clone())
        .or_default() // TODO: replace this with panic if the entry is not there
        .insert(
            mono_fn_id.clone(),
            ast::FunDecl {
                sig: ast::FunSig {
                    name: fun.sig.name.set_node(mono_fn_id.clone()),
                    type_params: vec![],
                    self_: fun.sig.self_,
                    params,
                    return_ty,
                },
                body: None,
            },
        );

    // Monomorphise function body.
    let body = match &fun.body {
        Some(body) => body,
        None => return mono_fn_id,
    };

    let mono_body = body.map_as_ref(|lstmts| mono_lstmts(lstmts, &ty_map, poly_pgm, mono_pgm));

    mono_pgm
        .associated
        .entry(mono_ty_id.clone())
        .or_default()
        .get_mut(&mono_fn_id)
        .unwrap()
        .body = Some(mono_body);

    mono_fn_id
}

fn mono_ty_decl(
    ty_decl: &ast::TypeDecl,
    args: &[ast::Type],
    poly_pgm: &PgmGraph,
    mono_pgm: &mut PgmGraph,
) -> Id {
    assert_eq!(ty_decl.type_params.len(), args.len());

    let mono_ty_id = mono_id(&ty_decl.name, args);

    // Check if we've already monomorphised this type.
    if mono_pgm.ty.contains_key(&mono_ty_id) {
        return mono_ty_id;
    }

    // Add current type to mono_pgm without a RHS to avoid looping.
    mono_pgm.ty.insert(
        mono_ty_id.clone(),
        ast::TypeDecl {
            name: mono_ty_id.clone(),
            type_params: vec![],
            rhs: None,
        },
    );

    // Maps type parameters of the type to type arguments.
    let ty_map: Map<Id, ast::Type> = ty_decl
        .type_params
        .iter()
        .cloned()
        .zip(args.iter().cloned())
        .collect();

    let rhs = ty_decl.rhs.as_ref().map(|rhs| match rhs {
        ast::TypeDeclRhs::Sum(constrs) => ast::TypeDeclRhs::Sum(
            constrs
                .iter()
                .map(|constr| mono_constr(constr, &ty_map, poly_pgm, mono_pgm))
                .collect(),
        ),

        ast::TypeDeclRhs::Product(fields) => {
            ast::TypeDeclRhs::Product(mono_fields(fields, &ty_map, poly_pgm, mono_pgm))
        }
    });

    mono_pgm.ty.get_mut(&mono_ty_id).unwrap().rhs = rhs;

    mono_ty_id
}

fn mono_constr(
    constr: &ast::ConstructorDecl,
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PgmGraph,
    mono_pgm: &mut PgmGraph,
) -> ast::ConstructorDecl {
    ast::ConstructorDecl {
        name: constr.name.clone(),
        fields: mono_fields(&constr.fields, ty_map, poly_pgm, mono_pgm),
    }
}

fn mono_fields(
    fields: &ast::ConstructorFields,
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PgmGraph,
    mono_pgm: &mut PgmGraph,
) -> ast::ConstructorFields {
    match fields {
        ast::ConstructorFields::Empty => ast::ConstructorFields::Empty,

        ast::ConstructorFields::Named(fields) => ast::ConstructorFields::Named(
            fields
                .iter()
                .map(|(name, ty)| (name.clone(), mono_ty(ty, ty_map, poly_pgm, mono_pgm)))
                .collect(),
        ),

        ast::ConstructorFields::Unnamed(fields) => ast::ConstructorFields::Unnamed(
            fields
                .iter()
                .map(|ty| mono_ty(ty, ty_map, poly_pgm, mono_pgm))
                .collect(),
        ),
    }
}

fn mono_ty(
    ty: &ast::Type,
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PgmGraph,
    mono_pgm: &mut PgmGraph,
) -> ast::Type {
    match ty {
        ast::Type::Named(ast::NamedType { name, args }) => {
            if let Some(mono_ty) = ty_map.get(name) {
                // Type is a monomorphised type varible. Since type variables kind `*` args should
                // be empty. (kinds are checked by the type checker)
                assert!(args.is_empty());
                return mono_ty.clone();
            }

            let args: Vec<ast::L<(Option<Id>, ast::L<ast::Type>)>> = args
                .iter()
                .map(|name_arg| {
                    name_arg.map_as_ref(|(name, arg)| {
                        (
                            name.clone(),
                            arg.map_as_ref(|arg| mono_ty(arg, ty_map, poly_pgm, mono_pgm)),
                        )
                    })
                })
                .collect();

            let ty_decl = poly_pgm.ty.get(name).unwrap();

            let mono_args: Vec<ast::Type> = args
                .iter()
                .filter_map(|ty| match ty.node.0 {
                    Some(_) => {
                        // Skip associated types: we ignore them during trait search, and methods have
                        // access to their associated types.
                        None
                    }
                    None => Some(ty.node.1.node.clone()),
                })
                .collect();

            let mono_ty_decl = mono_ty_decl(ty_decl, &mono_args, poly_pgm, mono_pgm);

            ast::Type::Named(ast::NamedType {
                name: mono_ty_decl,
                args: vec![],
            })
        }

        ast::Type::Record(args) => {
            if args.is_empty() {
                ast::Type::Record(vec![])
            } else {
                todo!()
            }
        }
    }
}

fn ty_name(ty: &ast::Type) -> &'static str {
    match ty {
        ast::Type::Named(ast::NamedType { name, args }) => match name.as_str() {
            "i8" | "u8" => {
                assert!(args.is_empty());
                "I8"
            }
            "i32" | "u32" => {
                assert!(args.is_empty());
                "U32"
            }
            "i64" | "u64" => {
                assert!(args.is_empty());
                "U64"
            }
            _ => "Ptr",
        },
        ast::Type::Record(_) => "Ptr",
    }
}

fn mono_id(name: &Id, tys: &[ast::Type]) -> Id {
    let mut mono_name = String::new();
    mono_name.push_str(name.as_str());
    for ty in tys {
        mono_name.push('@');
        mono_name.push_str(ty_name(ty));
    }
    SmolStr::new(mono_name)
}

// `ty_map` maps type constructors and varibles to mono types.
//
// Single map for both constructor and variables as variables can shadow constructors.
fn ty_to_ast(ty: &Ty, ty_map: &Map<Id, ast::Type>) -> ast::Type {
    match ty {
        Ty::Con(con) => ty_map.get(con).cloned().unwrap_or_else(|| {
            ast::Type::Named(ast::NamedType {
                name: con.clone(),
                args: vec![],
            })
        }),

        Ty::Var(_var) => {
            // Ambiguous type, monomorphise as unit.
            ast::Type::Record(vec![])
        }

        Ty::App(con, args) => {
            assert!(!ty_map.contains_key(con));
            ast::Type::Named(ast::NamedType {
                name: con.clone(),
                args: match args {
                    TyArgs::Positional(args) => args
                        .iter()
                        .map(|ty| ast::L {
                            loc: ast::Loc::dummy(),
                            node: (
                                None,
                                ast::L {
                                    loc: ast::Loc::dummy(),
                                    node: ty_to_ast(ty, ty_map),
                                },
                            ),
                        })
                        .collect(),
                    TyArgs::Named(args) => args
                        .iter()
                        .map(|(name, ty)| ast::L {
                            loc: ast::Loc::dummy(),
                            node: (
                                Some(name.clone()),
                                ast::L {
                                    loc: ast::Loc::dummy(),
                                    node: ty_to_ast(ty, ty_map),
                                },
                            ),
                        })
                        .collect(),
                },
            })
        }

        Ty::Record(_fields) => todo!(),

        Ty::QVar(_var) => panic!(),

        Ty::Fun(_args, _ret) => todo!(),

        Ty::FunNamedArgs(_args, _ret) => todo!(),

        Ty::AssocTySelect { ty: _, assoc_ty: _ } => todo!(),
    }
}
