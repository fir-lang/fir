/*!
This module implements monomorphisation based on base types: signed and unsigned 8-bit and 32-bit
numbers, and pointers.

The goal is to avoid boxing numbers. (and maybe in the future: chars, bools etc.)

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
type Vec@I8:
    data: Array@I8
    len: U32

type Vec@Ptr:
    data: Array@Ptr
    len: U32

fn print@I8@Ptr(a: I8, b: Ptr) = ...
fn print@I64@I64(a: I64, b: I64) = ...
```
*/

use crate::ast::{self, Id};
use crate::collections::{Map, Set};
use crate::interpolation::StringPart;
use crate::type_checker::{Kind, RecordOrVariant, Ty, TyArgs};

use smol_str::SmolStr;

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
                let old = top.insert(fun_decl.node.name.node.clone(), fun_decl.node);
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
                                .insert(fun_decl.name.node.clone(), fun_decl);
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

pub fn monomorphise(pgm: &[ast::L<ast::TopDecl>], main: &str) -> Vec<ast::L<ast::TopDecl>> {
    let poly_pgm = pgm_to_graph(pgm.iter().map(|decl| decl.node.clone()).collect());
    let mut mono_pgm = PgmGraph::default();

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
        make_ast_ty("Array", vec!["Str"]), // Array@Ptr
    ] {
        mono_ty(&ty, &Default::default(), &poly_pgm, &mut mono_pgm);
    }

    let main = poly_pgm
        .top
        .get(main)
        .unwrap_or_else(|| panic!("Main function `{}` not defined", main));
    mono_top_fn(main, &[], &poly_pgm, &mut mono_pgm);

    let mono_pgm = graph_to_pgm(mono_pgm);

    mono_pgm
        .into_iter()
        .map(|decl| ast::L {
            loc: ast::Loc::dummy(),
            node: decl,
        })
        .collect()
}

fn make_ast_ty(con: &'static str, args: Vec<&'static str>) -> ast::Type {
    ast::Type::Named(ast::NamedType {
        name: SmolStr::new_static(con),
        args: args
            .into_iter()
            .map(|arg| ast::L {
                loc: ast::Loc::dummy(),
                node: (
                    None,
                    ast::L {
                        loc: ast::Loc::dummy(),
                        node: ast::Type::Named(ast::NamedType {
                            name: SmolStr::new_static(arg),
                            args: vec![],
                        }),
                    },
                ),
            })
            .collect(),
    })
}

fn mono_top_fn(
    fun_decl: &ast::FunDecl,
    ty_args: &[ast::Type],
    poly_pgm: &PgmGraph,
    mono_pgm: &mut PgmGraph,
) -> Id {
    assert_eq!(fun_decl.sig.type_params.len(), ty_args.len());

    let mono_fn_id = mono_id(&fun_decl.name.node, ty_args);

    // Check if we've already monomorphised this function.
    if mono_pgm.top.contains_key(&mono_fn_id) {
        return mono_fn_id;
    }

    // Add current function to mono_pgm without a body to avoid looping.
    let ty_map: Map<Id, ast::Type> = fun_decl
        .sig
        .type_params
        .iter()
        .map(|ty_param| ty_param.id.node.clone())
        .zip(ty_args.iter().cloned())
        .collect();

    let params: Vec<(Id, ast::L<ast::Type>)> = fun_decl
        .sig
        .params
        .iter()
        .map(|(param_name, param_ty)| {
            (
                param_name.clone(),
                mono_l_ty(param_ty, &ty_map, poly_pgm, mono_pgm),
            )
        })
        .collect();

    let return_ty: Option<ast::L<ast::Type>> =
        mono_opt_l_ty(&fun_decl.sig.return_ty, &ty_map, poly_pgm, mono_pgm);

    mono_pgm.top.insert(
        mono_fn_id.clone(),
        ast::FunDecl {
            name: fun_decl.name.set_node(mono_fn_id.clone()),
            sig: ast::FunSig {
                type_params: vec![],
                self_: fun_decl.sig.self_,
                params,
                return_ty,
                exceptions: None,
            },
            body: None,
        },
    );

    // Monomorphise function body.
    let body = match &fun_decl.body {
        Some(body) => body,
        None => return mono_fn_id,
    };

    let mono_body = mono_lstmts(body, &ty_map, poly_pgm, mono_pgm);

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
        ast::Stmt::Break { label, level } => ast::Stmt::Break {
            label: label.clone(),
            level: *level,
        },

        ast::Stmt::Continue { label, level } => ast::Stmt::Continue {
            label: label.clone(),
            level: *level,
        },

        ast::Stmt::Let(ast::LetStmt { lhs, ty, rhs }) => ast::Stmt::Let(ast::LetStmt {
            lhs: mono_l_pat(lhs, ty_map, poly_pgm, mono_pgm),
            ty: mono_opt_l_ty(ty, ty_map, poly_pgm, mono_pgm),
            rhs: mono_l_expr(rhs, ty_map, poly_pgm, mono_pgm),
        }),

        ast::Stmt::Assign(ast::AssignStmt { lhs, rhs, op }) => ast::Stmt::Assign(ast::AssignStmt {
            lhs: mono_l_expr(lhs, ty_map, poly_pgm, mono_pgm),
            rhs: mono_l_expr(rhs, ty_map, poly_pgm, mono_pgm),
            op: *op,
        }),

        ast::Stmt::Expr(expr) => ast::Stmt::Expr(mono_l_expr(expr, ty_map, poly_pgm, mono_pgm)),

        ast::Stmt::For(ast::ForStmt {
            label,
            pat,
            ty,
            expr,
            expr_ty,
            body,
        }) => {
            // Interpreter will call `next` on `expr`, monomorphise the `next` member.
            let mono_expr_ty = mono_ty(
                &ty_to_ast(expr_ty.as_ref().unwrap(), ty_map),
                ty_map,
                poly_pgm,
                mono_pgm,
            );

            mono_method(
                expr_ty.as_ref().unwrap(),
                &SmolStr::new_static("next"),
                // `next` doesn't throw, pass empty row.
                &[Ty::Anonymous {
                    labels: Default::default(),
                    extension: None,
                    kind: RecordOrVariant::Record,
                    is_row: true,
                }],
                ty_map,
                poly_pgm,
                mono_pgm,
            );

            ast::Stmt::For(ast::ForStmt {
                label: label.clone(),
                pat: mono_l_pat(pat, ty_map, poly_pgm, mono_pgm),
                ty: mono_opt_l_ty(ty, ty_map, poly_pgm, mono_pgm),
                expr: expr.map_as_ref(|expr| mono_expr(expr, ty_map, poly_pgm, mono_pgm)),
                expr_ty: Some(mono_ast_ty_to_ty(&mono_expr_ty)),
                body: mono_lstmts(body, ty_map, poly_pgm, mono_pgm),
            })
        }

        ast::Stmt::While(ast::WhileStmt { label, cond, body }) => {
            ast::Stmt::While(ast::WhileStmt {
                label: label.clone(),
                cond: mono_l_expr(cond, ty_map, poly_pgm, mono_pgm),
                body: mono_lstmts(body, ty_map, poly_pgm, mono_pgm),
            })
        }

        ast::Stmt::WhileLet(ast::WhileLetStmt {
            label,
            pat,
            cond,
            body,
        }) => ast::Stmt::WhileLet(ast::WhileLetStmt {
            label: label.clone(),
            pat: mono_l_pat(pat, ty_map, poly_pgm, mono_pgm),
            cond: mono_l_expr(cond, ty_map, poly_pgm, mono_pgm),
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
        ast::Expr::Var(ast::VarExpr { id: var, ty_args }) => {
            let poly_decl = match poly_pgm.top.get(var) {
                Some(poly_decl) => poly_decl,
                None => {
                    // Local variable, cannot be polymorphic.
                    assert!(ty_args.is_empty());
                    return ast::Expr::Var(ast::VarExpr {
                        id: var.clone(),
                        ty_args: vec![],
                    });
                }
            };

            let mono_decl_id = mono_top_fn(
                poly_decl,
                &ty_args
                    .iter()
                    .map(|ty| ty_to_ast(ty, ty_map))
                    .collect::<Vec<_>>(),
                poly_pgm,
                mono_pgm,
            );

            ast::Expr::Var(ast::VarExpr {
                id: mono_decl_id,
                ty_args: vec![],
            })
        }

        ast::Expr::Constr(ast::ConstrExpr { id, ty_args }) => {
            let poly_ty_decl = match poly_pgm.ty.get(id) {
                None => panic!("Unknown constructor {}", id),
                Some(ty_decl) => ty_decl,
            };

            let mono_ty_id = mono_ty_decl(
                poly_ty_decl,
                &ty_args
                    .iter()
                    .map(|ty| ty_to_ast(ty, ty_map))
                    .collect::<Vec<_>>(),
                poly_pgm,
                mono_pgm,
            );

            ast::Expr::Constr(ast::ConstrExpr {
                id: mono_ty_id,
                ty_args: vec![],
            })
        }

        ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field }) => {
            // TODO: When the field is a method we should monomorphise here it to add it to the mono pgm.
            ast::Expr::FieldSelect(ast::FieldSelectExpr {
                object: mono_bl_expr(object, ty_map, poly_pgm, mono_pgm),
                field: field.clone(),
            })
        }

        ast::Expr::MethodSelect(ast::MethodSelectExpr {
            object,
            object_ty,
            method,
            ty_args,
        }) => {
            let (mono_method_id, mono_object_ty) = mono_method(
                object_ty.as_ref().unwrap(),
                method,
                ty_args,
                ty_map,
                poly_pgm,
                mono_pgm,
            );
            let mono_object = mono_bl_expr(object, ty_map, poly_pgm, mono_pgm);
            ast::Expr::MethodSelect(ast::MethodSelectExpr {
                object: mono_object,
                object_ty: Some(mono_ast_ty_to_ty(&mono_object_ty)),
                method: mono_method_id,
                ty_args: vec![],
            })
        }

        ast::Expr::ConstrSelect(ast::ConstrSelectExpr {
            ty,
            constr,
            ty_args,
        }) => {
            let poly_ty_decl = poly_pgm.ty.get(ty).unwrap();
            let mono_ty_id = mono_ty_decl(
                poly_ty_decl,
                &ty_args
                    .iter()
                    .map(|ty| ty_to_ast(ty, ty_map))
                    .collect::<Vec<_>>(),
                poly_pgm,
                mono_pgm,
            );
            ast::Expr::ConstrSelect(ast::ConstrSelectExpr {
                ty: mono_ty_id,
                constr: constr.clone(),
                ty_args: vec![],
            })
        }

        ast::Expr::AssocFnSelect(ast::AssocFnSelectExpr {
            ty,
            member,
            ty_args,
        }) => {
            let ty_decl = poly_pgm.ty.get(ty).unwrap();
            let ty_num_type_params = ty_decl.type_params.len();

            let mono_ty_args: Vec<ast::Type> = ty_args
                .iter()
                .map(|ty_arg| mono_ty(&ty_to_ast(ty_arg, ty_map), ty_map, poly_pgm, mono_pgm))
                .collect();

            let mono_ty_id = mono_ty_decl(
                ty_decl,
                &mono_ty_args[0..ty_num_type_params],
                poly_pgm,
                mono_pgm,
            );

            let fun_decl = poly_pgm.associated.get(ty).unwrap().get(member).unwrap();

            let assoc_fn_ty_map: Map<Id, ast::Type> = ty_decl
                .type_params
                .iter()
                .cloned()
                .zip(mono_ty_args.iter().cloned())
                .collect();

            let mono_fun_id = mono_assoc_fn(
                &mono_ty_id,
                fun_decl,
                &assoc_fn_ty_map,
                &mono_ty_args[ty_num_type_params..],
                poly_pgm,
                mono_pgm,
            );

            ast::Expr::AssocFnSelect(ast::AssocFnSelectExpr {
                ty: mono_ty_id,
                member: mono_fun_id,
                ty_args: vec![],
            })
        }

        ast::Expr::Int(int @ ast::IntExpr { suffix, .. }) => {
            let ty_decl_id = match suffix.unwrap() {
                ast::IntKind::I8 => "I8",
                ast::IntKind::U8 => "U8",
                ast::IntKind::I32 => "I32",
                ast::IntKind::U32 => "U32",
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

        ast::Expr::Self_ => ast::Expr::Self_,

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
            op: *op,
        }),

        ast::Expr::UnOp(ast::UnOpExpr { op, expr }) => ast::Expr::UnOp(ast::UnOpExpr {
            op: op.clone(),
            expr: mono_bl_expr(expr, ty_map, poly_pgm, mono_pgm),
        }),

        ast::Expr::Record(fields) => ast::Expr::Record(
            fields
                .iter()
                .map(|named_field| {
                    named_field.map_as_ref(|field| mono_l_expr(field, ty_map, poly_pgm, mono_pgm))
                })
                .collect(),
        ),

        ast::Expr::Variant(ast::VariantExpr { id, args }) => ast::Expr::Variant(ast::VariantExpr {
            id: id.clone(),
            args: args
                .iter()
                .map(|arg| arg.map_as_ref(|arg| mono_l_expr(arg, ty_map, poly_pgm, mono_pgm)))
                .collect(),
        }),

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
                        pattern: mono_l_pat(pattern, ty_map, poly_pgm, mono_pgm),
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

        ast::Expr::Fn(ast::FnExpr { sig, body, idx }) => {
            assert!(sig.type_params.is_empty());
            assert!(!sig.self_);
            assert_eq!(*idx, 0);
            ast::Expr::Fn(ast::FnExpr {
                sig: ast::FunSig {
                    type_params: vec![],
                    self_: false,
                    params: sig
                        .params
                        .iter()
                        .map(|(arg, ty)| (arg.clone(), mono_l_ty(ty, ty_map, poly_pgm, mono_pgm)))
                        .collect(),
                    return_ty: mono_opt_l_ty(&sig.return_ty, ty_map, poly_pgm, mono_pgm),
                    exceptions: mono_opt_l_ty(&sig.exceptions, ty_map, poly_pgm, mono_pgm),
                },
                body: mono_lstmts(body, ty_map, poly_pgm, mono_pgm),
                idx: 0,
            })
        }
    }
}

fn mono_method(
    poly_receiver_ty: &Ty,
    method: &Id,
    method_ty_args: &[Ty],
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PgmGraph,
    mono_pgm: &mut PgmGraph,
) -> (Id, ast::Type) {
    let poly_object_ty = ty_to_ast(poly_receiver_ty, ty_map);

    let mono_object_ty = mono_ty(&poly_object_ty, ty_map, poly_pgm, mono_pgm);

    let mono_receiver_ty_id = match &mono_object_ty {
        ast::Type::Named(ast::NamedType { name, args }) => {
            assert!(args.is_empty());
            name
        }

        ast::Type::Var(_) => panic!(),

        ast::Type::Record { .. } | ast::Type::Variant { .. } | ast::Type::Fn(_) => {
            // syntactically invalid, can't happen
            panic!()
        }
    };

    match &poly_object_ty {
        ast::Type::Named(ast::NamedType { name, args }) => {
            let ty_con = poly_pgm.ty.get(name).unwrap();
            assert_eq!(ty_con.type_params.len(), args.len());

            let fun = poly_pgm
                .associated
                .get(name)
                .unwrap_or_else(|| {
                    panic!(
                        "poly_pgm doesn't associated types for type {} (looking for method {})",
                        name, method
                    )
                })
                .get(method)
                .unwrap();

            let mut assoc_fn_ty_map = ty_map.clone();
            for (ty_param, ty_arg) in ty_con.type_params.iter().zip(args.iter()) {
                assoc_fn_ty_map.insert(ty_param.clone(), ty_arg.node.1.node.clone());
            }

            let mono_ty_args: Vec<ast::Type> = method_ty_args
                .iter()
                .map(|ty_arg| {
                    mono_ty(
                        &ty_to_ast(ty_arg, ty_map),
                        &assoc_fn_ty_map,
                        poly_pgm,
                        mono_pgm,
                    )
                })
                .collect();

            (
                mono_assoc_fn(
                    mono_receiver_ty_id,
                    fun,
                    &assoc_fn_ty_map,
                    &mono_ty_args,
                    poly_pgm,
                    mono_pgm,
                ),
                mono_object_ty,
            )
        }
        ast::Type::Var(_) => panic!(),
        ast::Type::Record { .. } => panic!(),
        ast::Type::Variant { .. } => panic!(),
        ast::Type::Fn(_) => panic!(),
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

fn mono_pat(
    pat: &ast::Pat,
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PgmGraph,
    mono_pgm: &mut PgmGraph,
) -> ast::Pat {
    match pat {
        // TODO: Can `Var` be a constructor like `Vec`?
        ast::Pat::Var(_)
        | ast::Pat::Ignore
        | ast::Pat::Str(_)
        | ast::Pat::Char(_)
        | ast::Pat::StrPfx(_, _) => pat.clone(),

        ast::Pat::Or(pat1, pat2) => ast::Pat::Or(
            mono_bl_pat(pat1, ty_map, poly_pgm, mono_pgm),
            mono_bl_pat(pat2, ty_map, poly_pgm, mono_pgm),
        ),

        ast::Pat::Constr(ast::ConstrPattern {
            constr: ast::Constructor { type_, constr },
            fields,
            ty_args,
        }) => {
            let ty_decl = poly_pgm.ty.get(type_).unwrap();

            let mono_ty_args: Vec<ast::Type> = ty_args
                .iter()
                .map(|ty_arg| mono_ty(&ty_to_ast(ty_arg, ty_map), ty_map, poly_pgm, mono_pgm))
                .collect();

            let mono_ty_id = mono_ty_decl(
                ty_decl,
                &mono_ty_args[0..ty_decl.type_params.len()],
                poly_pgm,
                mono_pgm,
            );

            let mono_fields = fields
                .iter()
                .map(|field| mono_named_l_pat(field, ty_map, poly_pgm, mono_pgm))
                .collect();

            ast::Pat::Constr(ast::ConstrPattern {
                constr: ast::Constructor {
                    type_: mono_ty_id,
                    constr: constr.clone(),
                },
                fields: mono_fields,
                ty_args: vec![],
            })
        }

        ast::Pat::Record(fields) => ast::Pat::Record(
            fields
                .iter()
                .map(|named_pat| mono_named_l_pat(named_pat, ty_map, poly_pgm, mono_pgm))
                .collect(),
        ),

        ast::Pat::Variant(ast::VariantPattern { constr, fields }) => {
            ast::Pat::Variant(ast::VariantPattern {
                constr: constr.clone(),
                fields: fields
                    .iter()
                    .map(|ast::Named { name, node }| ast::Named {
                        name: name.clone(),
                        node: mono_l_pat(node, ty_map, poly_pgm, mono_pgm),
                    })
                    .collect(),
            })
        }
    }
}

fn mono_l_pat(
    pat: &ast::L<ast::Pat>,
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PgmGraph,
    mono_pgm: &mut PgmGraph,
) -> ast::L<ast::Pat> {
    pat.map_as_ref(|pat| mono_pat(pat, ty_map, poly_pgm, mono_pgm))
}

fn mono_bl_pat(
    pat: &ast::L<ast::Pat>,
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PgmGraph,
    mono_pgm: &mut PgmGraph,
) -> Box<ast::L<ast::Pat>> {
    Box::new(mono_l_pat(pat, ty_map, poly_pgm, mono_pgm))
}

fn mono_named_l_pat(
    pat: &ast::Named<ast::L<ast::Pat>>,
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PgmGraph,
    mono_pgm: &mut PgmGraph,
) -> ast::Named<ast::L<ast::Pat>> {
    pat.map_as_ref(|pat| mono_l_pat(pat, ty_map, poly_pgm, mono_pgm))
}

/// Monomorphise an associated function or method.
///
/// `ty_map` maps type parameters of the type to mono types.
///
/// `ty_args` should not include the type's arguments, it should only have the function's type
/// arguments.
fn mono_assoc_fn(
    mono_ty_id: &Id,
    fun_decl: &ast::FunDecl,
    ty_map: &Map<Id, ast::Type>,
    ty_args: &[ast::Type],
    poly_pgm: &PgmGraph,
    mono_pgm: &mut PgmGraph,
) -> Id {
    let mono_fn_id = mono_id(&fun_decl.name.node, ty_args);

    if mono_pgm
        .associated
        .entry(mono_ty_id.clone())
        .or_default()
        .contains_key(&mono_fn_id)
    {
        return mono_fn_id;
    }

    let mut ty_map = ty_map.clone();
    let fun_ty_params = &fun_decl.sig.type_params[fun_decl.sig.type_params.len() - ty_args.len()..];
    for (ty_param, mono_ty) in fun_ty_params
        .iter()
        .map(|ty_param| ty_param.id.node.clone())
        .zip(ty_args.iter().cloned())
    {
        ty_map.insert(ty_param, mono_ty);
    }

    if fun_decl.sig.self_ {
        ty_map.insert(
            SmolStr::new("self"),
            ast::Type::Named(ast::NamedType {
                name: mono_ty_id.clone(),
                args: vec![],
            }),
        );
    }

    let params: Vec<(Id, ast::L<ast::Type>)> = fun_decl
        .sig
        .params
        .iter()
        .map(|(param_name, param_ty)| {
            (
                param_name.clone(),
                mono_l_ty(param_ty, &ty_map, poly_pgm, mono_pgm),
            )
        })
        .collect();

    let return_ty: Option<ast::L<ast::Type>> =
        mono_opt_l_ty(&fun_decl.sig.return_ty, &ty_map, poly_pgm, mono_pgm);

    mono_pgm
        .associated
        .entry(mono_ty_id.clone())
        .or_default() // TODO: replace this with panic if the entry is not there
        .insert(
            mono_fn_id.clone(),
            ast::FunDecl {
                name: fun_decl.name.set_node(mono_fn_id.clone()),
                sig: ast::FunSig {
                    type_params: vec![],
                    self_: fun_decl.sig.self_,
                    params,
                    return_ty,
                    exceptions: None,
                },
                body: None,
            },
        );

    // Monomorphise function body.
    let body = match &fun_decl.body {
        Some(body) => body,
        None => return mono_fn_id,
    };

    let mono_body = mono_lstmts(body, &ty_map, poly_pgm, mono_pgm);

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

            let ty_decl = poly_pgm
                .ty
                .get(name)
                .unwrap_or_else(|| panic!("Unbound type {}", name));

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

        ast::Type::Var(var) => ty_map
            .get(var)
            .unwrap_or_else(|| panic!("Unbound type variable {}", var))
            .clone(),

        ast::Type::Record { fields, extension } => {
            let mut names: Set<&Id> = Default::default();
            for field in fields {
                if let Some(name) = &field.name {
                    let new = names.insert(name);
                    if !new {
                        panic!("Record has duplicate fields: {:?}", fields);
                    }
                }
            }

            let mut fields: Vec<ast::Named<ast::Type>> = fields
                .iter()
                .map(|named_ty| named_ty.map_as_ref(|ty| mono_ty(ty, ty_map, poly_pgm, mono_pgm)))
                .collect();

            if let Some(extension) = extension {
                match ty_map.get(extension) {
                    Some(ast::Type::Record {
                        fields: extra_fields,
                        extension,
                    }) => {
                        assert!(extension.is_none());
                        fields.extend(extra_fields.iter().cloned());
                    }
                    other => panic!("Record extension is not a record: {:?}", other),
                }
            }

            ast::Type::Record {
                fields,
                extension: None,
            }
        }

        ast::Type::Variant { alts, extension } => {
            let mut cons: Set<&Id> = Default::default();
            for ast::VariantAlt { con, .. } in alts {
                let new = cons.insert(con);
                if !new {
                    panic!("Variant has duplicate constructors: {:?}", alts);
                }
            }

            let mut alts: Vec<ast::VariantAlt> = alts
                .iter()
                .map(|ast::VariantAlt { con, fields }| ast::VariantAlt {
                    con: con.clone(),
                    fields: fields
                        .iter()
                        .map(|ast::Named { name, node }| ast::Named {
                            name: name.clone(),
                            node: mono_ty(node, ty_map, poly_pgm, mono_pgm),
                        })
                        .collect(),
                })
                .collect();

            if let Some(extension) = extension {
                match ty_map.get(extension) {
                    Some(ast::Type::Variant {
                        alts: extra_alts,
                        extension,
                    }) => {
                        assert!(extension.is_none());
                        alts.extend(extra_alts.iter().cloned());
                    }
                    other => panic!("Variant extension is not a variant: {:?}", other),
                }
            }

            ast::Type::Variant {
                alts,
                extension: None,
            }
        }

        ast::Type::Fn(ast::FnType {
            args,
            ret,
            exceptions: _,
        }) => ast::Type::Fn(ast::FnType {
            args: args
                .iter()
                .map(|arg| arg.map_as_ref(|ty| mono_ty(ty, ty_map, poly_pgm, mono_pgm)))
                .collect(),
            ret: ret.as_ref().map(|ret| {
                ret.map_as_ref(|ret| Box::new(mono_ty(ret, ty_map, poly_pgm, mono_pgm)))
            }),
            exceptions: None,
        }),
    }
}

fn mono_l_ty(
    ty: &ast::L<ast::Type>,
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PgmGraph,
    mono_pgm: &mut PgmGraph,
) -> ast::L<ast::Type> {
    ty.map_as_ref(|ty| mono_ty(ty, ty_map, poly_pgm, mono_pgm))
}

fn mono_opt_l_ty(
    ty: &Option<ast::L<ast::Type>>,
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PgmGraph,
    mono_pgm: &mut PgmGraph,
) -> Option<ast::L<ast::Type>> {
    ty.as_ref()
        .map(|ty| mono_l_ty(ty, ty_map, poly_pgm, mono_pgm))
}

fn ty_name(ty: &ast::Type) -> &str {
    match ty {
        ast::Type::Named(ast::NamedType { name, args }) => match name.as_str() {
            "I8" | "U8" | "I32" | "U32" => {
                assert!(args.is_empty());
                name
            }
            _ => "Ptr",
        },
        ast::Type::Var(_) => "Ptr",
        ast::Type::Record { .. } | ast::Type::Variant { .. } => "Ptr",
        ast::Type::Fn(_) => "Ptr",
    }
}

fn mono_id(name: &Id, tys: &[ast::Type]) -> Id {
    let mut mono_name = String::new();
    mono_name.push_str(name);
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

        Ty::Var(var) => {
            // Ambiguous type, monomorphise as unit.
            match var.kind() {
                Kind::Star | Kind::Row(RecordOrVariant::Record) => ast::Type::Record {
                    fields: vec![],
                    extension: None,
                },
                Kind::Row(RecordOrVariant::Variant) => ast::Type::Variant {
                    alts: vec![],
                    extension: None,
                },
            }
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

        Ty::Anonymous {
            labels,
            extension: _,
            kind,
            is_row: _,
        } => {
            // TODO: Extension should be `None` or ambiguous.
            // assert!(extension.is_none(), "{:?}", extension);
            match kind {
                RecordOrVariant::Record => ast::Type::Record {
                    fields: labels
                        .iter()
                        .map(|(label_id, label_ty)| ast::Named {
                            name: Some(label_id.clone()),
                            node: ty_to_ast(label_ty, ty_map),
                        })
                        .collect(),
                    extension: None,
                },

                RecordOrVariant::Variant => {
                    // TODO FIXME: We can't distinguish a variant with a record field from a variant
                    // with multiple fields.
                    ast::Type::Variant {
                        alts: labels
                            .iter()
                            .map(|(con_label, con_fields)| ast::VariantAlt {
                                con: con_label.clone(),
                                fields: match ty_to_ast(con_fields, ty_map) {
                                    ast::Type::Record {
                                        fields,
                                        extension: _,
                                    } => fields,
                                    _ => panic!(),
                                },
                            })
                            .collect(),
                        extension: None,
                    }
                }
            }
        }

        Ty::Fun { .. } => todo!(),

        Ty::QVar(var) => {
            // We never create a QVar from the AST types, and type arguments to poly functions
            // should be instantiated types. So we should never see a QVAr.
            panic!("QVar {} in monomorphiser", var)
        }

        Ty::AssocTySelect { ty, assoc_ty } => {
            // Associated types should've been normalized away.
            panic!("Associated type {}.{} in monomorphiser", ty, assoc_ty)
        }
    }
}

fn mono_ast_ty_to_ty(mono_ast_ty: &ast::Type) -> Ty {
    match mono_ast_ty {
        ast::Type::Named(ast::NamedType { name, args }) => {
            assert!(args.is_empty());
            Ty::Con(name.clone())
        }
        ast::Type::Var(_) => todo!(),
        ast::Type::Record { .. } => todo!(),
        ast::Type::Variant { .. } => todo!(),
        ast::Type::Fn(_) => todo!(),
    }
}
