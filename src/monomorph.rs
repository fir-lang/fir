/*
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

```
type Vec[t]:
    data: Array[t]
    len: U32

fn print[ToStr[t1], ToStr[t2]](a: t1, b: t2) = ...
```

can be monomorphised to these variants:

```
type Vec@I8:
    data: Array@I8
    len: U32

type Vec@Ptr:
    data: Array@Ptr
    len: U32

fn print@I8@Ptr(a: I8, b: Ptr) = ...
fn print@I64@I64(a: I64, b: I64) = ...
```

## Trait example

```
let x: Vec[U32] = Vec.withCapacity(10)

let y: VecIter[U32] = x.iter()
    # MethodSelect { object_ty: Vec[U32], method_ty_id: Vec, method: iter, ty_args: [U32, ?exn] }

let z: Option[U32] = y.next()
    # MethodSelect { object_ty: VecIter[U32], method_ty_id: Iterator, method: next, ty_args: [VecIter[U32], ?exn] }

==>

method env = {
    Vec@U32: {
        iter: ...
    }
    VecIter@U32: {
        next: ...
    }
}

let x: Vec@U32 = ...
let y: VecIter@U32 = x.iter()
let z: Option@U32 = y.next()
```

Another example:

```
let x: CharIter = "asdf".chars()
    # MethodSelect { object_ty: Str, method_ty_id: Str, method: chars, ty_args: [?exn] }

let y: Map[CharIter, Char, U32] = x.map(fn(x: Char) { x.asU32() })
    # MethodSelect { object_ty: CharIter, method_ty_id: Iterator, method: map, ty_args: [CharIter, Char, U32, ?exn] }

let z: Option[U32] = y.next()
    # MethodSelect { object_ty: Map[CharIter, Char, U32], method_ty_id: Iterator, method: next, ty_args: [Map[CharIter, Char, U32], U32, ?exn] }

==>

method env = {
    Str: {
        chars: ...
    }
    CharIter: {
        map: ...
    }
    Map@CharIter@Char@U32: {
        next: ...
    }
}

let x: CharIter = "asdf".chars()
let y: Map@CharIter@Char@U32 = x.map(fn(x: Char) { x.asU32() })
let z: Option@U32 = y.next()
```

## Method example

```
let x: Str = "..."
let y: Bool = x.startsWith("...")
    # MethodSelect { object_ty: Str, method_ty_id: Str, method: startsWith, ty_args: [?exn] }
```

## Type syntax

In this pass we work with the AST types, because AST types are simpler (they don't have unification
variables).

For the fields that the type checker fills in as `Ty`, we convert to AST `Type`.

TODO: Do we use `object_ty`?
*/

use crate::ast::{self, Id};
use crate::collections::*;
use crate::interpolation::StringPart;
use crate::mono_ast as mono;
use crate::type_checker::{Kind, RecordOrVariant, Ty};
use crate::utils::*;

use smol_str::SmolStr;

/// The program in front-end syntax, converted to a graph for efficient and easy lookups.
#[derive(Debug)]
struct PolyPgm {
    traits: Map<Id, PolyTrait>,
    top: Map<Id, ast::FunDecl>,
    associated: Map<Id, Map<Id, ast::FunDecl>>,
    method: Map<Id, Map<Id, ast::FunDecl>>,
    ty: Map<Id, ast::TypeDecl>,
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

#[derive(Debug, Default)]
pub struct MonoPgm {
    pub funs: Map<Id, mono::FunDecl>,
    pub associated: Map<Id, Map<Id, mono::FunDecl>>,
    pub ty: Map<Id, mono::TypeDecl>,
}

fn pgm_to_poly_pgm(pgm: Vec<ast::TopDecl>) -> PolyPgm {
    let mut traits: Map<Id, PolyTrait> = Default::default();
    let mut top: Map<Id, ast::FunDecl> = Default::default();
    let mut associated: Map<Id, Map<Id, ast::FunDecl>> = Default::default();
    let mut method: Map<Id, Map<Id, ast::FunDecl>> = Default::default();
    let mut ty: Map<Id, ast::TypeDecl> = Default::default();

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
        make_ast_ty("Array", vec!["Str"]), // Array@Ptr
    ] {
        mono_ty(&ty, &Default::default(), &poly_pgm, &mut mono_pgm);
    }

    /*
    let main = poly_pgm
        .top
        .get(main)
        .unwrap_or_else(|| panic!("Main function `{}` not defined", main));

    mono_top_fn(main, &[], &poly_pgm, &mut mono_pgm);
    */

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
    ty_args: &[ast::Type],
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> Id {
    println!(
        "mono_top_fn {:?}.{}",
        &fun_decl.parent_ty, &fun_decl.name.node
    );

    assert_eq!(fun_decl.sig.context.type_params.len(), ty_args.len());

    let mono_fn_id = mono_id(&fun_decl.name.node, ty_args);

    // Check if we've already monomorphised this function.
    if mono_pgm.funs.contains_key(&mono_fn_id) {
        return mono_fn_id;
    }

    // Add current function to mono_pgm without a body to avoid looping.
    let ty_map: Map<Id, ast::Type> = fun_decl
        .sig
        .context
        .type_params
        .iter()
        .map(|(ty_param, _)| ty_param.clone())
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

    mono_pgm.funs.insert(
        mono_fn_id.clone(),
        ast::FunDecl {
            parent_ty: None,
            name: fun_decl.name.set_node(mono_fn_id.clone()),
            sig: ast::FunSig {
                context: ast::Context::default(),
                self_: fun_decl.sig.self_.clone(),
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

    mono_pgm.funs.get_mut(&mono_fn_id).unwrap().body = Some(mono_body);

    mono_fn_id
}

fn mono_stmt(
    stmt: &ast::Stmt,
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
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

        ast::Stmt::Let(ast::LetStmt { lhs, ty, rhs }) => mono::Stmt::Let(mono::LetStmt {
            lhs: mono_l_pat(lhs, ty_map, poly_pgm, mono_pgm),
            ty: mono_opt_l_ty(ty, ty_map, poly_pgm, mono_pgm),
            rhs: mono_l_expr(rhs, ty_map, poly_pgm, mono_pgm),
        }),

        ast::Stmt::Assign(ast::AssignStmt { lhs, rhs, op }) => {
            mono::Stmt::Assign(mono::AssignStmt {
                lhs: mono_l_expr(lhs, ty_map, poly_pgm, mono_pgm),
                rhs: mono_l_expr(rhs, ty_map, poly_pgm, mono_pgm),
                op: *op,
            })
        }

        ast::Stmt::Expr(expr) => mono::Stmt::Expr(mono_l_expr(expr, ty_map, poly_pgm, mono_pgm)),

        ast::Stmt::For(ast::ForStmt {
            label,
            pat,
            ty,
            expr,
            expr_ty,
            body,
        }) => {
            // Interpreter will call `next` on `expr`, monomorphise the `next` member.
            let mono_iter_ty = mono_ty(
                &ty_to_ast(expr_ty.as_ref().unwrap(), ty_map),
                ty_map,
                poly_pgm,
                mono_pgm,
            );

            let mono_item_ty = match ty {
                Some(ty) => mono_ty(&ty.node, ty_map, poly_pgm, mono_pgm),
                None => panic!("{}: For loop does have type annotation", loc_display(loc)),
            };

            mono_method(
                &SmolStr::new_static("Iterator"),
                &SmolStr::new_static("next"),
                &[
                    mono_iter_ty,
                    mono_item_ty,
                    ast::Type::Variant {
                        alts: vec![],
                        extension: None,
                    },
                ],
                ty_map,
                poly_pgm,
                mono_pgm,
            );

            mono::Stmt::For(mono::ForStmt {
                label: label.clone(),
                pat: mono_l_pat(pat, ty_map, poly_pgm, mono_pgm),
                expr: expr
                    .map_as_ref(|expr_| mono_expr(expr_, ty_map, poly_pgm, mono_pgm, &expr.loc)),
                body: mono_lstmts(body, ty_map, poly_pgm, mono_pgm),
            })
        }

        ast::Stmt::While(ast::WhileStmt { label, cond, body }) => {
            mono::Stmt::While(mono::WhileStmt {
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
        }) => mono::Stmt::WhileLet(mono::WhileLetStmt {
            label: label.clone(),
            pat: mono_l_pat(pat, ty_map, poly_pgm, mono_pgm),
            cond: mono_l_expr(cond, ty_map, poly_pgm, mono_pgm),
            body: mono_lstmts(body, ty_map, poly_pgm, mono_pgm),
        }),
    }
}

// ty_map: maps type variables in scope to their mono types.
fn mono_expr(
    expr: &ast::Expr,
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
    loc: &ast::Loc,
) -> mono::Expr {
    println!("{}: {:?}", loc_display(loc), expr);
    println!("  ty_map: {:?}", ty_map);
    match expr {
        ast::Expr::Var(ast::VarExpr { id: var, ty_args }) => {
            let poly_decl = match poly_pgm.top.get(var) {
                Some(poly_decl) => poly_decl,
                None => {
                    // Local variable, cannot be polymorphic.
                    assert!(ty_args.is_empty());
                    return mono::Expr::Var(mono::VarExpr { id: var.clone() });
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

            mono::Expr::Var(mono::VarExpr { id: mono_decl_id })
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

            mono::Expr::Constr(mono::ConstrExpr { id: mono_ty_id })
        }

        ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field }) => {
            // TODO: When the field is a method we should monomorphise here it to add it to the mono pgm.
            mono::Expr::FieldSelect(mono::FieldSelectExpr {
                object: mono_bl_expr(object, ty_map, poly_pgm, mono_pgm),
                field: field.clone(),
            })
        }

        ast::Expr::MethodSelect(ast::MethodSelectExpr {
            object,       // receiver
            object_ty,    // receiver type
            method_ty_id, // type that the method belongs to: `trait` or `type`
            method,       // method or associated function name
            ty_args,      // function type arguments
        }) => {
            let mono_ty_args: Vec<ast::Type> =
                ty_args.iter().map(|ty| ty_to_ast(ty, ty_map)).collect();

            let mono_method_id = mono_method(
                method_ty_id,
                method,
                &mono_ty_args,
                ty_map,
                poly_pgm,
                mono_pgm,
            );

            let mono_object = mono_bl_expr(object, ty_map, poly_pgm, mono_pgm);

            let mono_object_ty = mono_ty(
                &ty_to_ast(object_ty.as_ref().unwrap(), ty_map),
                ty_map,
                poly_pgm,
                mono_pgm,
            );

            mono::Expr::MethodSelect(mono::MethodSelectExpr {
                object: mono_object,
                method_ty_id: method_ty_id.clone(),
                method_id: mono_method_id,
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
            mono::Expr::ConstrSelect(mono::ConstrSelectExpr {
                ty: mono_ty_id,
                constr: constr.clone(),
            })
        }

        ast::Expr::AssocFnSelect(ast::AssocFnSelectExpr {
            ty,
            member,
            ty_args,
        }) => {
            let mono_ty_args: Vec<ast::Type> = ty_args
                .iter()
                .map(|ty_arg| mono_ty(&ty_to_ast(ty_arg, ty_map), ty_map, poly_pgm, mono_pgm))
                .collect();

            let fun_decl = poly_pgm.associated.get(ty).unwrap().get(member).unwrap();

            let mono_fun_id = mono_top_fn(fun_decl, &mono_ty_args, poly_pgm, mono_pgm);

            mono::Expr::Var(mono::VarExpr { id: mono_fun_id })
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
            mono::Expr::Int(int.clone())
        }

        ast::Expr::Char(char) => {
            let ty_decl = poly_pgm.ty.get("Char").unwrap();
            mono_ty_decl(ty_decl, &[], poly_pgm, mono_pgm);
            mono::Expr::Char(*char)
        }

        ast::Expr::Self_ => mono::Expr::Self_,

        ast::Expr::Call(ast::CallExpr { fun, args }) => mono::Expr::Call(mono::CallExpr {
            fun: mono_bl_expr(fun, ty_map, poly_pgm, mono_pgm),
            args: args
                .iter()
                .map(|ast::CallArg { name, expr }| mono::CallArg {
                    name: name.clone(),
                    expr: mono_l_expr(expr, ty_map, poly_pgm, mono_pgm),
                })
                .collect(),
        }),

        ast::Expr::String(parts) => mono::Expr::String(
            parts
                .iter()
                .map(|part| match part {
                    StringPart::Str(str) => mono::StringPart::Str(str.clone()),
                    StringPart::Expr(expr) => {
                        mono::StringPart::Expr(mono_l_expr(expr, ty_map, poly_pgm, mono_pgm))
                    }
                })
                .collect(),
        ),

        ast::Expr::BinOp(ast::BinOpExpr { left, right, op }) => {
            mono::Expr::BinOp(mono::BinOpExpr {
                left: mono_bl_expr(left, ty_map, poly_pgm, mono_pgm),
                right: mono_bl_expr(right, ty_map, poly_pgm, mono_pgm),
                op: *op,
            })
        }

        ast::Expr::UnOp(ast::UnOpExpr { op, expr }) => mono::Expr::UnOp(mono::UnOpExpr {
            op: op.clone(),
            expr: mono_bl_expr(expr, ty_map, poly_pgm, mono_pgm),
        }),

        ast::Expr::Record(fields) => mono::Expr::Record(
            fields
                .iter()
                .map(|named_field| {
                    named_field.map_as_ref(|field| mono_l_expr(field, ty_map, poly_pgm, mono_pgm))
                })
                .collect(),
        ),

        ast::Expr::Variant(ast::VariantExpr { id, args }) => {
            mono::Expr::Variant(mono::VariantExpr {
                id: id.clone(),
                args: args
                    .iter()
                    .map(|arg| arg.map_as_ref(|arg| mono_l_expr(arg, ty_map, poly_pgm, mono_pgm)))
                    .collect(),
            })
        }

        ast::Expr::Return(expr) => {
            mono::Expr::Return(mono_bl_expr(expr, ty_map, poly_pgm, mono_pgm))
        }

        ast::Expr::Match(ast::MatchExpr { scrutinee, alts }) => {
            mono::Expr::Match(mono::MatchExpr {
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
            })
        }

        ast::Expr::If(ast::IfExpr {
            branches,
            else_branch,
        }) => mono::Expr::If(mono::IfExpr {
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
            assert!(sig.context.type_params.is_empty());
            assert!(matches!(sig.self_, ast::SelfParam::No));
            assert_eq!(*idx, 0);
            mono::Expr::Fn(mono::FnExpr {
                sig: mono::FunSig {
                    self_: mono::SelfParam::No,
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

// Monomorphise a trait or non-trait method.
//
// Example for traits: `x.next` where `x: Map[Chars, Char, U32]`.
//
// - method_ty_id: `Iterator`
// - method_id: `next`
// - ty_args: `[Map[Chars, Char, U32], U32]` (type arguments to `Iterator`)
//
// Example for non-traits: `x.push` where `x: Vec[U32]`.
//
// - method_ty_id: `Vec`
// - method_id: `push`
// - ty_args: `[U32]`
fn mono_method(
    method_ty_id: &Id,     // type that the method belonds to: `trait` or `type`
    method_id: &Id,        // method name
    ty_args: &[ast::Type], // method mono type arguments, including the trait or type's
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> Id {
    println!(
        "mono_method method_ty_id={}, method_id={}, ty_args={:?}",
        method_ty_id, method_id, ty_args
    );

    let mono_method_id = mono_id(method_ty_id, ty_args);

    if mono_pgm.funs.contains_key(&mono_method_id) {
        return mono_method_id;
    }

    if let Some(PolyTrait {
        ty_args: trait_ty_args,
        impls,
    }) = poly_pgm.traits.get(method_ty_id)
    {
        // Find the matching impl.
        for impl_ in impls {
            if let Some(substs) = match_trait_impl(&ty_args[0..trait_ty_args.len()], impl_) {
                let method: &ast::FunDecl = impl_
                    .methods
                    .iter()
                    .find(|fun_decl| &fun_decl.name.node == method_id)
                    .unwrap();

                let mut ty_map = ty_map.clone();
                ty_map.extend(substs);

                let params: Vec<(Id, ast::L<ast::Type>)> = method
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
                    mono_opt_l_ty(&method.sig.return_ty, &ty_map, poly_pgm, mono_pgm);

                // Isn't used by the interpreter, can be used when debugging.
                let mono_trait_id = mono_id(method_ty_id, &ty_args[..trait_ty_args.len()]);

                mono_pgm.funs.insert(
                    mono_method_id.clone(),
                    ast::FunDecl {
                        parent_ty: Some(ast::L {
                            node: mono_trait_id.clone(),
                            loc: ast::Loc::dummy(),
                        }),
                        name: method.name.set_node(mono_method_id.clone()),
                        sig: ast::FunSig {
                            context: ast::Context::default(),
                            self_: method.sig.self_.clone(),
                            params,
                            return_ty,
                            exceptions: None,
                        },
                        body: None,
                    },
                );

                // Monomorphise method body.
                let body = match &method.body {
                    Some(body) => body,
                    None => return mono_method_id,
                };

                let mono_body = mono_lstmts(body, &ty_map, poly_pgm, mono_pgm);

                mono_pgm.funs.get_mut(&mono_method_id).unwrap().body = Some(mono_body);

                return mono_method_id;
            }
        }

        panic!(
            "Unable to find matching impl for {} type args {:?}",
            method_ty_id, ty_args
        );
    }

    if let Some(method_map) = poly_pgm.method.get(method_ty_id) {
        let method: &ast::FunDecl = method_map.get(method_id).unwrap();

        let params: Vec<(Id, ast::L<ast::Type>)> = method
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
            mono_opt_l_ty(&method.sig.return_ty, &ty_map, poly_pgm, mono_pgm);

        // Isn't used by the interpreter, can be used when debugging.
        let method_ty_params = method.sig.context.type_params.len();
        let method_parent_ty_id =
            mono_id(method_ty_id, &ty_args[..ty_args.len() - method_ty_params]);

        mono_pgm.funs.insert(
            mono_method_id.clone(),
            ast::FunDecl {
                parent_ty: Some(ast::L {
                    node: method_parent_ty_id.clone(),
                    loc: ast::Loc::dummy(),
                }),
                name: method.name.set_node(mono_method_id.clone()),
                sig: ast::FunSig {
                    context: ast::Context::default(),
                    self_: method.sig.self_.clone(),
                    params,
                    return_ty,
                    exceptions: None,
                },
                body: None,
            },
        );

        // Monomorphise method body.
        let body = match &method.body {
            Some(body) => body,
            None => return mono_method_id,
        };

        let mono_body = mono_lstmts(body, &ty_map, poly_pgm, mono_pgm);

        mono_pgm.funs.get_mut(&mono_method_id).unwrap().body = Some(mono_body);

        return mono_method_id;
    }

    panic!("Type {} is not a trait or type", method_ty_id)
}

fn mono_lstmts(
    lstmts: &[ast::L<ast::Stmt>],
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> Vec<ast::L<mono::Stmt>> {
    lstmts
        .iter()
        .map(|lstmt| {
            lstmt.map_as_ref(|stmt| mono_stmt(stmt, ty_map, poly_pgm, mono_pgm, &lstmt.loc))
        })
        .collect()
}

fn mono_bl_expr(
    expr: &ast::L<ast::Expr>,
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> Box<ast::L<mono::Expr>> {
    Box::new(expr.map_as_ref(|expr_| mono_expr(expr_, ty_map, poly_pgm, mono_pgm, &expr.loc)))
}

fn mono_l_expr(
    expr: &ast::L<ast::Expr>,
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> ast::L<mono::Expr> {
    expr.map_as_ref(|expr_| mono_expr(expr_, ty_map, poly_pgm, mono_pgm, &expr.loc))
}

fn mono_pat(
    pat: &ast::Pat,
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> mono::Pat {
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
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> ast::L<mono::Pat> {
    pat.map_as_ref(|pat| mono_pat(pat, ty_map, poly_pgm, mono_pgm))
}

fn mono_bl_pat(
    pat: &ast::L<ast::Pat>,
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> Box<ast::L<ast::Pat>> {
    Box::new(mono_l_pat(pat, ty_map, poly_pgm, mono_pgm))
}

fn mono_named_l_pat(
    pat: &ast::Named<ast::L<ast::Pat>>,
    ty_map: &Map<Id, ast::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> ast::Named<ast::L<ast::Pat>> {
    pat.map_as_ref(|pat| mono_l_pat(pat, ty_map, poly_pgm, mono_pgm))
}

/// Monomorphise an associated function or method.
///
/// `ty_map` maps type parameters of the type to mono types.
fn mono_assoc_fn(
    mono_ty_id: &Id,
    fun_decl: &ast::FunDecl,
    ty_map: &Map<Id, ast::Type>,
    ty_args: &[ast::Type],
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> Id {
    println!("mono_assoc_fn {}.{}", mono_ty_id, &fun_decl.name.node);
    println!("  ty_args: {:?}", ty_args);
    println!("  ty_map: {:?}", ty_map);

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
    let fun_ty_params =
        &fun_decl.sig.context.type_params[fun_decl.sig.context.type_params.len() - ty_args.len()..];
    for (ty_param, mono_ty) in fun_ty_params
        .iter()
        .map(|(ty_param, _)| ty_param.clone())
        .zip(ty_args.iter().cloned())
    {
        ty_map.insert(ty_param, mono_ty);
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
                parent_ty: Some(ast::L {
                    node: mono_ty_id.clone(),
                    loc: ast::Loc::dummy(),
                }),
                name: fun_decl.name.set_node(mono_fn_id.clone()),
                sig: ast::FunSig {
                    context: ast::Context::default(),
                    self_: fun_decl.sig.self_.clone(),
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

fn mono_l_ty(
    ty: &ast::L<ast::Type>,
    ty_map: &Map<Id, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> ast::L<mono::Type> {
    ty.map_as_ref(|ty| mono_ast_ty(ty, ty_map, poly_pgm, mono_pgm))
}

fn mono_opt_l_ty(
    ty: &Option<ast::L<ast::Type>>,
    ty_map: &Map<Id, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> Option<ast::L<mono::Type>> {
    ty.as_ref()
        .map(|ty| mono_l_ty(ty, ty_map, poly_pgm, mono_pgm))
}

/// Convert a type-checking type to mono AST type.
///
/// `ty_map` maps type constructors and varibles to mono types.
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
                args: args
                    .iter()
                    .map(|ty| ast::L {
                        loc: ast::Loc::dummy(),
                        node: ty_to_ast(ty, ty_map),
                    })
                    .collect(),
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

////////////////////////////////////////////////////////////////////////////////////////////////////
// Trait matching

fn match_trait_impl(
    ty_args: &[ast::Type],
    trait_impl: &PolyTraitImpl,
) -> Option<Map<Id, ast::Type>> {
    debug_assert_eq!(ty_args.len(), trait_impl.tys.len(), "{:?}", ty_args);

    println!("Trying to match impl:");
    println!("  impl tys: {:?}", &trait_impl.tys);
    println!("  ty args:  {:?}", ty_args);

    let mut substs: Map<Id, ast::Type> = Default::default();
    for (trait_ty, ty_arg) in trait_impl.tys.iter().zip(ty_args.iter()) {
        if !match_(trait_ty, ty_arg, &mut substs) {
            return dbg!(None);
        }
    }

    dbg!(Some(substs))
}

fn match_(trait_ty: &ast::Type, arg_ty: &ast::Type, substs: &mut Map<Id, ast::Type>) -> bool {
    match (trait_ty, arg_ty) {
        (
            ast::Type::Named(ast::NamedType {
                name: name1,
                args: args1,
            }),
            ast::Type::Named(ast::NamedType {
                name: name2,
                args: args2,
            }),
        ) => {
            if name1 != name2 {
                return false;
            }
            debug_assert_eq!(args1.len(), args2.len());

            for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                if !match_(&arg1.node, &arg2.node, substs) {
                    return false;
                }
            }

            true
        }

        _ => false,
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Types

/// Monomorphise a type-checking type.
fn mono_tc_ty(
    ty: &Ty,
    ty_map: &Map<Id, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> mono::Type {
    match ty {
        Ty::Var(var) => panic!("Type variable: {:?}", var),

        Ty::Con(con) => {
            let ty_decl = poly_pgm.ty.get(con).unwrap();
            mono::Type::Named(mono_ty_decl(ty_decl, &[], poly_pgm, mono_pgm))
        }

        Ty::App(con, args) => {
            let ty_decl = poly_pgm.ty.get(con).unwrap();
            let mono_args: Vec<mono::Type> = args
                .iter()
                .map(|arg| mono_tc_ty(arg, ty_map, poly_pgm, mono_pgm))
                .collect();
            mono::Type::Named(mono_ty_decl(ty_decl, &mono_args, poly_pgm, mono_pgm))
        }

        Ty::QVar(var) => ty_map.get(var).unwrap().clone(),

        Ty::Fun {
            args: _,
            ret: _,
            exceptions: _,
        } => {
            todo!()
        }

        Ty::Anonymous {
            labels: _,
            extension: _,
            kind: _,
            is_row: _,
        } => todo!(),
    }
}

fn mono_ast_ty(
    ty: &ast::Type,
    ty_map: &Map<Id, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> mono::Type {
    match ty {
        ast::Type::Named(ast::NamedType { name: con, args }) => {
            let ty_decl = poly_pgm.ty.get(con).unwrap();
            let mono_args: Vec<mono::Type> = args
                .iter()
                .map(|arg| mono_ast_ty(&arg.node, ty_map, poly_pgm, mono_pgm))
                .collect();
            mono::Type::Named(mono_ty_decl(ty_decl, &mono_args, poly_pgm, mono_pgm))
        }

        ast::Type::Var(var) => ty_map.get(var).unwrap().clone(),

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

            let mut fields: Vec<ast::Named<mono::Type>> = fields
                .iter()
                .map(|named_ty| named_ty.map_as_ref(|ty| mono_ty(ty, ty_map, poly_pgm, mono_pgm)))
                .collect();

            if let Some(extension) = extension {
                match ty_map.get(extension) {
                    Some(mono::Type::Record {
                        fields: extra_fields,
                    }) => {
                        fields.extend(extra_fields.iter().cloned());
                    }
                    other => panic!("Record extension is not a record: {:?}", other),
                }
            }

            mono::Type::Record { fields }
        }

        ast::Type::Variant { alts, extension } => {
            let mut cons: Set<&Id> = Default::default();
            for ast::VariantAlt { con, .. } in alts {
                let new = cons.insert(con);
                if !new {
                    panic!("Variant has duplicate constructors: {:?}", alts);
                }
            }

            let mut alts: Vec<mono::VariantAlt> = alts
                .iter()
                .map(|ast::VariantAlt { con, fields }| mono::VariantAlt {
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
                    Some(mono::Type::Variant { alts: extra_alts }) => {
                        alts.extend(extra_alts.iter().cloned());
                    }
                    other => panic!("Variant extension is not a variant: {:?}", other),
                }
            }

            mono::Type::Variant { alts }
        }

        ast::Type::Fn(ast::FnType {
            args,
            ret,
            exceptions: _,
        }) => mono::Type::Fn(mono::FnType {
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

/// Monomorphise a type declaration. Returns the name of the mono type.
fn mono_ty_decl(
    ty_decl: &ast::TypeDecl,
    args: &[mono::Type],
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
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
        mono::TypeDecl {
            name: mono_ty_id.clone(),
            rhs: None,
        },
    );

    // Maps type parameters of the type to type arguments.
    let ty_map: Map<Id, mono::Type> = ty_decl
        .type_params
        .iter()
        .cloned()
        .zip(args.iter().cloned())
        .collect();

    let rhs: Option<mono::TypeDeclRhs> = ty_decl.rhs.as_ref().map(|rhs| match rhs {
        ast::TypeDeclRhs::Sum(constrs) => mono::TypeDeclRhs::Sum(
            constrs
                .iter()
                .map(|constr| mono_constr(constr, &ty_map, poly_pgm, mono_pgm))
                .collect(),
        ),

        ast::TypeDeclRhs::Product(fields) => {
            mono::TypeDeclRhs::Product(mono_fields(fields, &ty_map, poly_pgm, mono_pgm))
        }
    });

    mono_pgm.ty.get_mut(&mono_ty_id).unwrap().rhs = rhs;

    mono_ty_id
}

fn mono_constr(
    constr: &ast::ConstructorDecl,
    ty_map: &Map<Id, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> mono::ConstructorDecl {
    mono::ConstructorDecl {
        name: constr.name.clone(),
        fields: mono_fields(&constr.fields, ty_map, poly_pgm, mono_pgm),
    }
}

fn mono_fields(
    fields: &ast::ConstructorFields,
    ty_map: &Map<Id, mono::Type>,
    poly_pgm: &PolyPgm,
    mono_pgm: &mut MonoPgm,
) -> mono::ConstructorFields {
    match fields {
        ast::ConstructorFields::Empty => mono::ConstructorFields::Empty,

        ast::ConstructorFields::Named(fields) => mono::ConstructorFields::Named(
            fields
                .iter()
                .map(|(name, ty)| (name.clone(), mono_ty(ty, ty_map, poly_pgm, mono_pgm)))
                .collect(),
        ),

        ast::ConstructorFields::Unnamed(fields) => mono::ConstructorFields::Unnamed(
            fields
                .iter()
                .map(|ty| mono_ty(ty, ty_map, poly_pgm, mono_pgm))
                .collect(),
        ),
    }
}

fn mono_id(name: &Id, tys: &[mono::Type]) -> Id {
    fn mono_ty_name(ty: &mono::Type) -> &str {
        match ty {
            mono::Type::Named(name) => name,
            mono::Type::Record { .. } | mono::Type::Variant { .. } => "Ptr",
            mono::Type::Fn(_) => "Ptr",
        }
    }
    let mut mono_name = String::new();
    mono_name.push_str(name);
    for ty in tys {
        mono_name.push('@');
        mono_name.push_str(mono_ty_name(ty));
    }
    SmolStr::new(mono_name)
}
