#![allow(clippy::mutable_key_type, clippy::for_kv_map)]

mod apply;
mod convert;
mod expr;
mod instantiation;
pub(crate) mod kind_inference;
mod pat;
mod pat_coverage;
pub(crate) mod row_utils;
mod stmt;
mod ty;
mod ty_map;
mod unification;

pub use crate::utils::loc_display;
use convert::convert_fields;
use convert::*;
use instantiation::normalize_instantiation_types;
use stmt::check_stmts;
use ty::*;
pub use ty::{Kind, RecordOrVariant, Ty, TyArgs};
use ty_map::TyMap;

use crate::ast::{self, Id};
use crate::collections::*;

use smol_str::SmolStr;

/// Type constructors and types in the program.
#[derive(Debug)]
pub struct PgmTypes {
    /// Type schemes of top-level functions.
    ///
    /// These functions don't take a `self` parameter and can't be called as methods.
    pub top_schemes: Map<Id, Scheme>,

    /// Type schemes of associated functions.
    ///
    /// These include methods (associated functions with a `self` parameter).
    pub associated_fn_schemes: Map<Id, Map<Id, Scheme>>,

    /// Type schemes of methods.
    ///
    /// These are associated functions (so they're also in `associated_fn_schemes`) that take a
    /// `self` parameter.
    ///
    /// The first parameters of the function types here are the `self` types.
    ///
    /// Because these schemes are only used in method call syntax, the keys are not type names but
    /// method names. The values are type schemes of methods with the name.
    pub method_schemes: Map<Id, Vec<Scheme>>,

    /// Type constructor details.
    pub tys: TyMap,
}

/// Type check a module.
///
/// Updates trait implementation blocks with the default implementations of missing methods.
///
/// Returns schemes of top-level functions, associated functions (includes trait methods), and
/// details of type constructors (`TyCon`).
pub fn check_module(module: &mut ast::Module) -> PgmTypes {
    add_exception_types(module);
    kind_inference::add_missing_type_params(module);
    let mut tys = collect_types(module);
    for decl in module {
        match &mut decl.node {
            ast::TopDecl::Import(_) => panic!(
                "{}: Import declaration in check_module",
                loc_display(&decl.loc)
            ),

            // Types and schemes added to `PgmTypes` by `collect_types`.
            ast::TopDecl::Type(_) | ast::TopDecl::Trait(_) => {}

            ast::TopDecl::Impl(impl_) => check_impl(impl_, &mut tys),

            ast::TopDecl::Fun(fun) => check_top_fun(fun, &mut tys),
        }
    }

    tys
}

/// Add exception types to functions without one.
fn add_exception_types(module: &mut ast::Module) {
    for decl in module {
        match &mut decl.node {
            ast::TopDecl::Fun(ast::L { node: fun, .. }) => {
                if fun.sig.exceptions.is_none() {
                    if fun.name.node == "main" {
                        fun.sig.exceptions = Some(ast::L {
                            node: ast::Type::Variant {
                                alts: Default::default(),
                                extension: None,
                            },
                            loc: ast::Loc::dummy(),
                        });
                    } else {
                        fun.sig.exceptions = Some(exn_type());
                    }
                }
            }

            ast::TopDecl::Trait(ast::L { node, .. }) => {
                for fun in &mut node.items {
                    if fun.node.sig.exceptions.is_none() {
                        fun.node.sig.exceptions = Some(exn_type());
                    }
                }
            }

            ast::TopDecl::Impl(ast::L { node, .. }) => {
                for fun in &mut node.items {
                    if fun.node.sig.exceptions.is_none() {
                        fun.node.sig.exceptions = Some(exn_type());
                    }
                }
            }

            ast::TopDecl::Import(_) | ast::TopDecl::Type(_) => {}
        }
    }
}

// The default exception type: `[..?exn]`.
fn exn_type() -> ast::L<ast::Type> {
    ast::L {
        node: ast::Type::Variant {
            alts: Default::default(),
            extension: Some(EXN_QVAR_ID),
        },
        loc: ast::Loc::dummy(),
    }
}

/// Type checking state for a single function (top-level, associated, or method).
struct TcFunState<'a> {
    /// Term environment.
    env: &'a mut ScopeMap<Id, Ty>,

    /// Type environment.
    tys: &'a mut PgmTypes,

    /// Unification variable generator.
    var_gen: &'a mut TyVarGen,

    /// Exception type of the current function.
    ///
    /// Exceptions thrown by called functions are unified with this type.
    ///
    /// For now we don't do exception type inference, so this will always be a concrete type (with
    /// rigid type variables).
    exceptions: Ty,

    /// Return type of the current function.
    ///
    /// This is used when checking expressions in return position: in `return` expressions, in the
    /// last statement of the function body etc.
    return_ty: Ty,

    /// Predicates generated when checking the function body.
    ///
    /// After checking the body, these predicates should all be resolved by the function context and
    /// trait environment (in `PgmTypes`).
    preds: &'a mut Set<Pred>,
}

const EXN_QVAR_ID: Id = SmolStr::new_static("?exn");

/// Collect type constructors (traits and data) and type schemes (top-level, associated, traits) of
/// the program.
///
/// Does not type check the code, only collects types and type schemes.
fn collect_types(module: &mut ast::Module) -> PgmTypes {
    let mut tys = collect_cons(module);
    let (top_schemes, associated_fn_schemes, method_schemes) = collect_schemes(module, &mut tys);
    PgmTypes {
        top_schemes,
        associated_fn_schemes,
        method_schemes,
        tys,
    }
}

fn collect_cons(module: &mut ast::Module) -> TyMap {
    let mut tys: TyMap = Default::default();

    // Collect all type constructors first, then add fields and methods.
    for decl in module.iter() {
        match &decl.node {
            ast::TopDecl::Type(ty_decl) => {
                assert_eq!(
                    ty_decl.node.type_params.len(),
                    ty_decl.node.type_param_kinds.len()
                );
                let ty_name = ty_decl.node.name.clone();
                if tys.has_con(&ty_name) {
                    panic!(
                        "{}: Type {} is defined multiple times",
                        loc_display(&decl.loc),
                        ty_name
                    );
                }
                tys.insert_con(
                    ty_name.clone(),
                    TyCon {
                        id: ty_name.clone(),
                        ty_params: ty_decl
                            .node
                            .type_params
                            .iter()
                            .cloned()
                            .zip(ty_decl.node.type_param_kinds.iter().cloned())
                            .collect(),
                        details: TyConDetails::Type(TypeDetails { cons: vec![] }),
                    },
                );
            }

            ast::TopDecl::Trait(trait_decl) => {
                assert_eq!(
                    trait_decl.node.type_params.len(),
                    trait_decl.node.type_param_kinds.len()
                );
                let ty_name = trait_decl.node.name.node.clone();
                if tys.has_con(&ty_name) {
                    panic!(
                        "{}: Type {} is defined multiple times",
                        loc_display(&decl.loc),
                        ty_name
                    );
                }

                tys.insert_con(
                    ty_name.clone(),
                    TyCon {
                        id: ty_name.clone(),
                        ty_params: trait_decl
                            .node
                            .type_params
                            .iter()
                            .map(|node| node.node.clone())
                            .zip(trait_decl.node.type_param_kinds.iter().cloned())
                            .collect(),
                        details: TyConDetails::Trait(TraitDetails {
                            methods: Default::default(),
                        }),
                    },
                );
            }

            ast::TopDecl::Import(_) | ast::TopDecl::Fun(_) | ast::TopDecl::Impl(_) => continue,
        }
    }

    // Add fields and methods.
    // This is where we start converting AST types to type checking types, so the ty con map should
    // be populated at this point.
    for decl in module.iter() {
        match &decl.node {
            ast::TopDecl::Type(ty_decl) => {
                let details = match &ty_decl.node.rhs {
                    Some(rhs) => match rhs {
                        ast::TypeDeclRhs::Sum(sum_cons) => {
                            let cons: Vec<ConShape> =
                                sum_cons.iter().map(ConShape::from_ast).collect();
                            TyConDetails::Type(TypeDetails { cons })
                        }

                        ast::TypeDeclRhs::Product(fields) => TyConDetails::Type(TypeDetails {
                            cons: vec![ConShape {
                                name: None,
                                fields: ConFieldShape::from_ast(fields),
                            }],
                        }),
                    },

                    None => TyConDetails::Type(TypeDetails { cons: vec![] }),
                };

                tys.get_con_mut(&ty_decl.node.name).unwrap().details = details;
            }

            ast::TopDecl::Trait(trait_decl) => {
                // New scope to be able to bind type variables in the context and associated types
                // before converting types.
                assert_eq!(tys.len_scopes(), 1);
                tys.enter_scope();

                assert_eq!(
                    trait_decl.node.type_params.len(),
                    trait_decl.node.type_param_kinds.len()
                );

                let trait_context_ast: ast::Context = ast::Context {
                    type_params: trait_decl
                        .node
                        .type_params
                        .iter()
                        .map(|id| id.node.clone())
                        .zip(trait_decl.node.type_param_kinds.iter().cloned())
                        .collect(),
                    preds: vec![],
                };

                let _trait_context: Set<Pred> =
                    convert_and_bind_context(&mut tys, &trait_context_ast, TyVarConversion::ToQVar);

                let methods: Map<Id, TraitMethod> = trait_decl
                    .node
                    .items
                    .iter()
                    .map(|fun| {
                        // New scope for function context.
                        tys.enter_scope();

                        let fun_preds: Set<Pred> = convert_and_bind_context(
                            &mut tys,
                            &fun.node.sig.context,
                            TyVarConversion::ToQVar,
                        );

                        let mut arg_tys: Vec<Ty> = fun
                            .node
                            .sig
                            .params
                            .iter()
                            .map(|(_name, ty)| convert_ast_ty(&tys, &ty.node, &ty.loc))
                            .collect();

                        match &fun.node.sig.self_ {
                            ast::SelfParam::No => {}
                            ast::SelfParam::Implicit => {
                                panic!(
                                    "{}: Trait methods can't have implicit self type",
                                    loc_display(&fun.loc)
                                );
                            }
                            ast::SelfParam::Explicit(ty) => {
                                arg_tys.insert(0, convert_ast_ty(&tys, &ty.node, &ty.loc));
                            }
                        }

                        let ret_ty: Ty = match &fun.node.sig.return_ty {
                            Some(ret_ty) => convert_ast_ty(&tys, &ret_ty.node, &ret_ty.loc),
                            None => Ty::unit(),
                        };

                        let exceptions = match &fun.node.sig.exceptions {
                            Some(ty) => convert_ast_ty(&tys, &ty.node, &ty.loc),
                            None => panic!(),
                        };

                        let fun_ty = Ty::Fun {
                            args: FunArgs::Positional(arg_tys),
                            ret: Box::new(ret_ty),
                            exceptions: Some(Box::new(exceptions)),
                        };

                        tys.exit_scope();

                        let scheme = Scheme {
                            quantified_vars: trait_decl
                                .node
                                .type_params
                                .iter()
                                .map(|id| id.node.clone())
                                .zip(trait_decl.node.type_param_kinds.iter().cloned())
                                .chain(fun.node.sig.context.type_params.iter().cloned())
                                .collect(),
                            preds: fun_preds,
                            ty: fun_ty,
                            loc: fun.loc.clone(),
                        };

                        (fun.node.name.node.clone(), {
                            TraitMethod {
                                scheme,
                                fun_decl: fun.clone(),
                            }
                        })
                    })
                    .collect();

                let ty_con = tys.get_con_mut(&trait_decl.node.name.node).unwrap();
                assert_eq!(ty_con.ty_params.len(), 1);

                ty_con.details = TyConDetails::Trait(TraitDetails { methods });

                tys.exit_scope();
                assert_eq!(tys.len_scopes(), 1);
            }

            ast::TopDecl::Fun(_) | ast::TopDecl::Import(_) | ast::TopDecl::Impl(_) => continue,
        }
    }

    // Add default methods to impls.
    //
    // We don't need to type check default methods copied to impls, but for now we do.
    for decl in module.iter_mut() {
        let impl_decl = match &mut decl.node {
            ast::TopDecl::Impl(impl_decl) => &mut impl_decl.node,
            _ => continue,
        };

        let trait_con_id = &impl_decl.trait_.node.clone();

        // New scope for the context.
        assert_eq!(tys.len_scopes(), 1);
        tys.enter_scope();

        /*
        let impl_var_kinds: Map<Id, Kind> = impl_decl
            .context
            .type_params
            .iter()
            .map(|(param, kind)| (param.clone(), kind.clone()))
            .collect();
        */

        let _impl_context =
            convert_and_bind_context(&mut tys, &impl_decl.context, TyVarConversion::ToQVar);

        let trait_ty_con = tys.get_con_mut(trait_con_id).unwrap_or_else(|| {
            panic!("{}: Unknown trait {}", loc_display(&decl.loc), trait_con_id)
        });

        let trait_type_params = &trait_ty_con.ty_params;

        let trait_methods = match &mut trait_ty_con.details {
            TyConDetails::Trait(TraitDetails { ref methods }) => methods,

            TyConDetails::Type { .. } | TyConDetails::Synonym(_) => {
                panic!(
                    "{}: {} in impl declararation is not a trait",
                    loc_display(&decl.loc),
                    trait_con_id
                );
            }
        };

        // Type constructor of the type implementing the trait.
        // TODO: We are passing empty con map here to avoid borrow checking issues. This will fail
        // when the trait arugment is a type synonym, which we should reject anyway, but with a
        // proper error message.
        // let (self_ty_con, _) = impl_ty.con(&Default::default()).unwrap();

        for (method, method_decl) in trait_methods {
            if impl_decl
                .items
                .iter()
                .any(|item| &item.node.name.node == method)
            {
                continue;
            }

            if method_decl.fun_decl.node.body.is_some() {
                let mut fun_decl = method_decl.fun_decl.clone();

                // Map type parameters of the trait to the impl types.
                let substs: Map<Id, ast::Type> = trait_type_params
                    .iter()
                    .map(|(param, _param_kind)| param.clone())
                    .zip(impl_decl.tys.iter().map(|ty| ty.node.clone()))
                    .collect();

                fun_decl.node.sig.params = fun_decl
                    .node
                    .sig
                    .params
                    .into_iter()
                    .map(|(param, param_ty)| (param, param_ty.map(|ty| ty.subst_ids(&substs))))
                    .collect();

                fun_decl.node.sig.exceptions = fun_decl
                    .node
                    .sig
                    .exceptions
                    .map(|exc| exc.map(|exc| exc.subst_ids(&substs)));

                fun_decl.node.sig.return_ty = fun_decl
                    .node
                    .sig
                    .return_ty
                    .map(|ret| ret.map(|ret| ret.subst_ids(&substs)));

                impl_decl.items.push(fun_decl);
            }
        }

        tys.exit_scope();
        assert_eq!(tys.len_scopes(), 1);
    }

    assert_eq!(tys.len_scopes(), 1);
    tys
}

// `ty_cons` is `mut` to be able to update it with associated types when checking traits.
fn collect_schemes(
    module: &ast::Module,
    tys: &mut TyMap,
) -> (
    Map<Id, Scheme>,
    Map<Id, Map<Id, Scheme>>,
    Map<Id, Vec<Scheme>>,
) {
    let mut top_schemes: Map<Id, Scheme> = Default::default();
    let mut associated_fn_schemes: Map<Id, Map<Id, Scheme>> = Default::default();
    let mut method_schemes: Map<Id, Vec<Scheme>> = Default::default();

    for decl in module {
        // New scope for type and function contexts.
        assert_eq!(tys.len_scopes(), 1);
        tys.enter_scope();

        match &decl.node {
            ast::TopDecl::Fun(ast::L {
                node:
                    ast::FunDecl {
                        parent_ty,
                        name,
                        sig,
                        body: _,
                    },
                loc,
            }) => {
                let fun_preds: Set<Pred> =
                    convert_and_bind_context(tys, &sig.context, TyVarConversion::ToQVar);

                let mut arg_tys: Vec<Ty> = sig
                    .params
                    .iter()
                    .map(|(_name, ty)| convert_ast_ty(tys, &ty.node, &ty.loc))
                    .collect();

                match sig.self_ {
                    ast::SelfParam::No => {}
                    ast::SelfParam::Implicit => {
                        // The parent type should have no type arguments.
                        match parent_ty {
                            Some(parent_ty) => {
                                let parent_ty_con = tys.get_con(&parent_ty.node).unwrap_or_else(||
                                    panic!("{}: Unknown type {}", loc_display(&decl.loc), &parent_ty.node));
                                if !parent_ty_con.ty_params.is_empty() {
                                    panic!(
                                        "{}: Can't infer `self` type as the parent type {} has type parameters",
                                        loc_display(&decl.loc),
                                        &parent_ty.node
                                    );
                                }
                                arg_tys.insert(0, Ty::Con(parent_ty_con.id.clone()));
                            }
                            None => panic!(
                                "{}: Function with `self` type needs to have to be an associated function",
                                loc_display(&decl.loc)
                            ),
                        }
                    }
                    ast::SelfParam::Explicit(ty) => {
                        arg_tys.insert(0, convert_ast_ty(tys, &ty.node, &ty.loc));
                    }
                }

                let ret_ty: Ty = match &sig.return_ty {
                    Some(ret_ty) => convert_ast_ty(tys, &ret_ty.node, &ret_ty.loc),
                    None => Ty::unit(),
                };

                let exceptions = match &sig.exceptions {
                    Some(ty) => convert_ast_ty(tys, &ty.node, &ty.loc),
                    None => panic!(),
                };

                let fun_ty = Ty::Fun {
                    args: FunArgs::Positional(arg_tys),
                    ret: Box::new(ret_ty),
                    exceptions: Some(Box::new(exceptions)),
                };

                let scheme = Scheme {
                    quantified_vars: sig.context.type_params.iter().cloned().collect(),
                    preds: fun_preds,
                    ty: fun_ty,
                    loc: loc.clone(),
                };

                match parent_ty {
                    Some(parent_ty) => {
                        let old = associated_fn_schemes
                            .entry(parent_ty.node.clone())
                            .or_default()
                            .insert(name.node.clone(), scheme);
                        if old.is_some() {
                            panic!(
                                "{}: {}.{} is defined multiple times",
                                loc_display(loc),
                                parent_ty.node,
                                name.node
                            );
                        }

                        match sig.self_ {
                            ast::SelfParam::No => {}
                            ast::SelfParam::Implicit | ast::SelfParam::Explicit(_) => {
                                method_schemes
                                    .entry(name.node.clone())
                                    .or_default()
                                    .push(scheme);
                            }
                        }
                    }
                    None => {
                        let old = top_schemes.insert(name.node.clone(), scheme);
                        if old.is_some() {
                            panic!(
                                "{}: {} is defined multiple times",
                                loc_display(loc),
                                name.node
                            );
                        }
                    }
                }
            }

            ast::TopDecl::Type(ty_decl) => {
                // Add constructors as functions.
                let rhs = match &ty_decl.node.rhs {
                    Some(rhs) => rhs,
                    None => {
                        tys.exit_scope();
                        continue;
                    }
                };

                // Bind type parameters in the context for constructor schemes.
                for ty_var in &ty_decl.node.type_params {
                    tys.insert_var(ty_var.clone(), Ty::QVar(ty_var.clone()));
                }

                let ty_vars: Set<Id> = ty_decl.node.type_params.iter().cloned().collect();

                // Return type of constructors.
                let ret = if ty_vars.is_empty() {
                    Ty::Con(ty_decl.node.name.clone())
                } else {
                    Ty::App(
                        ty_decl.node.name.clone(),
                        TyArgs::Positional(
                            ty_decl
                                .node
                                .type_params
                                .iter()
                                .map(|ty_var| Ty::QVar(ty_var.clone()))
                                .collect(),
                        ),
                    )
                };

                match rhs {
                    ast::TypeDeclRhs::Sum(cons) => {
                        for con in cons {
                            let fields = &con.fields;
                            // TODO: loc should be con loc, add loc to cons
                            let ty = match convert_fields(tys, fields, &ty_decl.loc) {
                                None => ret.clone(),
                                Some(ConFields::Unnamed(tys)) => Ty::Fun {
                                    args: FunArgs::Positional(tys),
                                    ret: Box::new(ret.clone()),
                                    exceptions: None,
                                },
                                Some(ConFields::Named(tys)) => Ty::Fun {
                                    args: FunArgs::Named(tys),
                                    ret: Box::new(ret.clone()),
                                    exceptions: None,
                                },
                            };
                            let var_kinds = constructor_decls_var_kinds(cons);
                            let scheme = Scheme {
                                quantified_vars: ty_decl
                                    .node
                                    .type_params
                                    .iter()
                                    .map(|ty_param| {
                                        (
                                            ty_param.clone(),
                                            QVar {
                                                kind: var_kinds
                                                    .get(ty_param)
                                                    .cloned()
                                                    .unwrap_or(Kind::Star),
                                                bounds: Default::default(),
                                            },
                                        )
                                    })
                                    .collect(),
                                ty,
                                loc: ty_decl.loc.clone(), // TODO: use con loc
                            };
                            let old = associated_fn_schemes
                                .entry(ty_decl.node.name.clone())
                                .or_default()
                                .insert(con.name.clone(), scheme);
                            if old.is_some() {
                                panic!(
                                    "{}: Constructor {}.{} is defined multiple times",
                                    loc_display(&ty_decl.loc), // TODO: use con loc
                                    ty_decl.node.name,
                                    con.name,
                                );
                            }
                        }
                    }
                    ast::TypeDeclRhs::Product(fields) => {
                        let ty = match convert_fields(tys, fields, &ty_decl.loc) {
                            None => ret,
                            Some(ConFields::Unnamed(tys)) => Ty::Fun {
                                args: FunArgs::Positional(tys),
                                ret: Box::new(ret.clone()),
                                exceptions: None,
                            },
                            Some(ConFields::Named(tys)) => Ty::Fun {
                                args: FunArgs::Named(tys),
                                ret: Box::new(ret.clone()),
                                exceptions: None,
                            },
                        };
                        let var_kinds = constructor_fields_var_kinds(fields);
                        let scheme = Scheme {
                            quantified_vars: ty_decl
                                .node
                                .type_params
                                .iter()
                                .map(|ty_param| {
                                    (
                                        ty_param.clone(),
                                        QVar {
                                            kind: var_kinds
                                                .get(ty_param)
                                                .cloned()
                                                .unwrap_or(Kind::Star),
                                            bounds: Default::default(),
                                        },
                                    )
                                })
                                .collect(),
                            ty,
                            loc: ty_decl.loc.clone(), // TODO: use con loc
                        };
                        let old = top_schemes.insert(ty_decl.node.name.clone(), scheme);
                        if old.is_some() {
                            panic!(
                                "{}: Constructor {} is defined multiple times",
                                loc_display(&ty_decl.loc), // TODO: use con loc
                                ty_decl.node.name,
                            );
                        }
                    }
                }
            }

            ast::TopDecl::Impl(_) | ast::TopDecl::Trait(_) | ast::TopDecl::Import(_) => {
                tys.exit_scope();
                continue;
            }
        }

        tys.exit_scope();
        assert_eq!(tys.len_scopes(), 1);
    }

    assert_eq!(tys.len_scopes(), 1);

    (top_schemes, associated_fn_schemes, method_schemes)
}

/// Type check a top-level function.
fn check_top_fun(fun: &mut ast::L<ast::FunDecl>, tys: &mut PgmTypes) {
    let mut var_gen = TyVarGen::default();
    let mut env: ScopeMap<Id, Ty> = ScopeMap::default();

    let scheme = tys.top_schemes.get(&fun.node.name.node).unwrap().clone();

    assert_eq!(tys.tys.len_scopes(), 1);
    tys.tys.enter_scope();

    let var_kinds = fun_sig_ty_var_kinds(&fun.node.sig);
    let fn_bounds = convert_and_bind_context(
        &mut tys.tys,
        &fun.node.sig.type_params,
        &var_kinds,
        TyVarConversion::ToOpaque,
        &fun.loc,
    );

    let old_method_schemes = bind_type_params(&fn_bounds, tys, &fun.loc);

    for (param_name, param_ty) in &fun.node.sig.params {
        env.insert(
            param_name.clone(),
            convert_ast_ty(&tys.tys, &param_ty.node, &fun.loc),
        );
    }

    let ret_ty = match &fun.node.sig.return_ty {
        Some(ty) => convert_ast_ty(&tys.tys, &ty.node, &ty.loc),
        None => Ty::unit(),
    };

    let mut preds: Set<Pred> = Default::default();

    let context = scheme.quantified_vars.iter().cloned().collect();

    let exceptions = match &fun.node.sig.exceptions {
        Some(exc) => convert_ast_ty(&tys.tys, &exc.node, &exc.loc),
        None => panic!(),
    };

    let mut tc_state = TcFunState {
        context: &context,
        return_ty: ret_ty.clone(),
        env: &mut env,
        var_gen: &mut var_gen,
        tys,
        preds: &mut preds,
        exceptions,
    };

    if let Some(body) = &mut fun.node.body.as_mut() {
        check_stmts(&mut tc_state, body, Some(&ret_ty), 0, &mut Vec::new());

        for stmt in body.iter_mut() {
            normalize_instantiation_types(&mut stmt.node, tys.tys.cons());
        }
    }

    resolve_all_preds(&context, tys, preds, &mut var_gen, 0);

    unbind_type_params(old_method_schemes, &mut tys.method_schemes);

    tys.tys.exit_scope();
}

/// Type check an `impl` block.
///
/// The block may be for a trait implementation or for associated functions.
///
/// `tys` is `mut` to be able to add type parameters of the `impl` and associated types before
/// checking the methods.
fn check_impl(impl_: &mut ast::L<ast::ImplDecl>, tys: &mut PgmTypes) {
    assert_eq!(tys.tys.len_scopes(), 1);
    tys.tys.enter_scope();

    // Bind trait type parameters.
    let impl_var_kinds: Map<Id, Kind> = impl_
        .node
        .context
        .iter()
        .map(|param| (param.id.node.clone(), Kind::Star))
        .collect();

    let impl_bounds = convert_and_bind_context(
        &mut tys.tys,
        &impl_.node.context,
        &impl_var_kinds,
        TyVarConversion::ToOpaque,
        &impl_.loc,
    );

    // Schemes overridden by trait bounds.
    let old_schemes_1 = bind_type_params(&impl_bounds, tys, &impl_.loc);

    let self_ty = convert_ast_ty(&tys.tys, &impl_.node.ty.node, &impl_.loc);

    // Bind associated types.
    bind_associated_types(impl_, &mut tys.tys);

    match &impl_.node.trait_ {
        Some(trait_ty_con_id) => {
            let trait_ty_con = tys.tys.get_con(&trait_ty_con_id.node).unwrap_or_else(|| {
                panic!(
                    "{}: Unknown trait {}",
                    loc_display(&trait_ty_con_id.loc),
                    trait_ty_con_id.node
                )
            });

            let trait_details = trait_ty_con
                .trait_details()
                .unwrap_or_else(|| {
                    panic!(
                        "{}: {} in `impl` block is not a trait",
                        loc_display(&trait_ty_con_id.loc),
                        trait_ty_con_id.node
                    )
                })
                .clone();

            // Check method bodies.
            for fun in &mut impl_.node.items {
                tys.tys.enter_scope();

                // Bind function type parameters.
                let var_kinds = fun_sig_ty_var_kinds(&fun.node.sig);
                let fn_bounds = convert_and_bind_context(
                    &mut tys.tys,
                    &fun.node.sig.context,
                    &var_kinds,
                    TyVarConversion::ToOpaque,
                    &impl_.loc,
                );

                // Schemes overridden by method bounds.
                let old_schemes_2 = bind_type_params(&fn_bounds, tys, &fun.loc);

                // Check the body.
                if let Some(body) = &mut fun.node.body {
                    let ret_ty = match &fun.node.sig.return_ty {
                        Some(ty) => convert_ast_ty(&tys.tys, &ty.node, &ty.loc),
                        None => Ty::unit(),
                    };

                    let mut preds: Set<Pred> = Default::default();
                    let mut env: ScopeMap<Id, Ty> = ScopeMap::default();
                    let mut var_gen = TyVarGen::default();

                    env.insert(SmolStr::new_static("self"), self_ty.clone());

                    for (param_name, param_ty) in &fun.sig.params {
                        env.insert(
                            param_name.clone(),
                            convert_ast_ty(&tys.tys, &param_ty.node, &item.loc),
                        );
                    }

                    let context = impl_bounds
                        .iter()
                        .cloned()
                        .chain(fn_bounds.into_iter())
                        .collect();

                    let exceptions = match &fun.sig.exceptions {
                        Some(exc) => convert_ast_ty(&tys.tys, &exc.node, &exc.loc),
                        None => panic!(),
                    };

                    let mut tc_state = TcFunState {
                        context: &context,
                        return_ty: ret_ty.clone(),
                        env: &mut env,
                        var_gen: &mut var_gen,
                        tys,
                        preds: &mut preds,
                        exceptions,
                    };

                    check_stmts(&mut tc_state, body, Some(&ret_ty), 0, &mut Vec::new());

                    for stmt in body.iter_mut() {
                        normalize_instantiation_types(&mut stmt.node, tys.tys.cons());
                    }

                    resolve_all_preds(&context, tys, preds, &mut var_gen, 0);
                }

                unbind_type_params(old_schemes_2, &mut tys.method_schemes);

                tys.tys.exit_scope();
            }

            // Check that all methods without default implementations are implemented.
            let trait_method_ids: Set<&Id> = trait_details.methods.keys().collect();
            let mut implemented_method_ids: Set<&Id> = Default::default();
            for fun in &impl_.node.items {
                let fun_id = &fun.node.name.node;
                match (
                    trait_method_ids.contains(fun_id),
                    implemented_method_ids.contains(fun_id),
                ) {
                    (true, true) => panic!(
                        "{}: Trait method {} implemented multiple times",
                        loc_display(&fun.loc),
                        fun_id
                    ),

                    (true, false) => {
                        implemented_method_ids.insert(fun_id);
                    }

                    (false, _) => {
                        panic!(
                            "{}: Trait {} does not have method {}",
                            loc_display(&item.loc),
                            trait_ty_con_id.node,
                            fun_id
                        )
                    }
                }
            }
            let missing_methods: Vec<&&Id> = trait_method_ids
                .difference(&implemented_method_ids)
                .collect();
            if !missing_methods.is_empty() {
                panic!(
                    "{}: Trait methods missing: {:?}",
                    loc_display(&impl_.loc),
                    missing_methods
                );
            }
        }

        None => {
            for fun in &mut impl_.node.items {
                assert_eq!(tys.tys.len_scopes(), 2); // top-level, impl
                tys.tys.enter_scope();

                // Bind function type parameters.
                let var_kinds = fun_sig_ty_var_kinds(&fun.node.sig);
                let fn_bounds: Vec<(Id, QVar)> = convert_and_bind_context(
                    &mut tys.tys,
                    &fun.node.sig.context,
                    &var_kinds,
                    TyVarConversion::ToOpaque,
                    &fun.loc,
                );

                // Schemes overridden by method bounds.
                let old_schemes_2 = bind_type_params(&fn_bounds, tys, &item.loc);

                // Check the body.
                if let Some(body) = &mut fun.node.body {
                    let ret_ty = match &fun.node.sig.return_ty {
                        Some(ty) => convert_ast_ty(&tys.tys, &ty.node, &ty.loc),
                        None => Ty::unit(),
                    };

                    let mut preds: Set<Pred> = Default::default();
                    let mut env: ScopeMap<Id, Ty> = ScopeMap::default();
                    let mut var_gen = TyVarGen::default();

                    env.insert(SmolStr::new_static("self"), self_ty.clone());

                    for (param_name, param_ty) in &fun.node.sig.params {
                        env.insert(
                            param_name.clone(),
                            convert_ast_ty(&tys.tys, &param_ty.node, &fun.loc),
                        );
                    }

                    let context = impl_bounds
                        .iter()
                        .map(|(qvar, details)| (qvar.clone(), details.clone()))
                        .chain(fn_bounds.into_iter())
                        .collect();

                    let exceptions = match &fun.node.sig.exceptions {
                        Some(exc) => convert_ast_ty(&tys.tys, &exc.node, &exc.loc),
                        None => panic!(),
                    };

                    let mut tc_state = TcFunState {
                        context: &context,
                        return_ty: ret_ty.clone(),
                        env: &mut env,
                        var_gen: &mut var_gen,
                        tys,
                        preds: &mut preds,
                        exceptions,
                    };

                    check_stmts(&mut tc_state, body, Some(&ret_ty), 0, &mut Vec::new());

                    for stmt in body.iter_mut() {
                        normalize_instantiation_types(&mut stmt.node, tys.tys.cons());
                    }

                    resolve_all_preds(&context, tys, preds, &mut var_gen, 0);
                }

                unbind_type_params(old_schemes_2, &mut tys.method_schemes);

                tys.tys.exit_scope();
                assert_eq!(tys.tys.len_scopes(), 2); // top-level, impl
            }
        }
    }

    unbind_type_params(old_schemes_1, &mut tys.method_schemes);

    tys.tys.exit_scope();
    assert_eq!(tys.tys.len_scopes(), 1);
}

/// We currently don't allow a type constructor to implement a trait multiple times with different
/// type arguments, e.g. `impl Debug[Vec[U32]]` and `impl Debug[Vec[Str]]` are not allowed at the
/// same time.
///
/// With this restriction resolving predicates is just a matter of checking for
/// `impl Trait[Con[T1, T2, ...]]` in the program, where `T1, T2, ...` are distrinct type variables.
fn resolve_preds(
    context: &Map<Id, QVar>,
    tys: &PgmTypes,
    preds: Set<Pred>,
    var_gen: &mut TyVarGen,
    level: u32,
) -> Set<Pred> {
    todo!()
    /*
    let mut remaining_preds: Set<Pred> = Default::default();

    for Pred {
        trait_,
        params,
        assoc_tys,
        loc,
    } in preds.into_iter()
    {
        let ty_var_ty = ty_var.normalize(tys.tys.cons());
        match &ty_var_ty {
            Ty::Con(con) | Ty::App(con, _) => {
                let TraitDetails {
                    implementing_tys, ..
                } = tys
                    .tys
                    .cons()
                    .get(&trait_)
                    .unwrap_or_else(|| {
                        panic!(
                            "{}: BUG: Trait {} is not in the environment",
                            loc_display(&loc),
                            trait_
                        )
                    })
                    .trait_details()
                    .unwrap_or_else(|| {
                        panic!(
                            "{}: BUG: {} in predicates is not a trait",
                            loc_display(&loc),
                            trait_
                        )
                    });

                if !implementing_tys.contains(con)
                    && context.get(con).map(|ctx| ctx.bounds.contains_key(&trait_)) != Some(true)
                {
                    panic!(
                        "{}: Type {} does not implement trait {}",
                        loc_display(&loc),
                        con,
                        trait_
                    );
                }

                // Substitute quantified variables in the type constructor with the type arguments.
                let args = match &ty_var_ty {
                    Ty::App(_, TyArgs::Positional(args)) => args,
                    _ => &vec![],
                };

                let con_qvars: Vec<Id> = tys
                    .tys
                    .get_con(con)
                    .unwrap()
                    .ty_params
                    .iter()
                    .map(|(qvar, _)| qvar.clone())
                    .collect();

                let qvar_map: Map<Id, Ty> = con_qvars
                    .into_iter()
                    .zip(args.iter())
                    .map(|(var, ty)| (var, ty.clone()))
                    .collect();

                for (assoc_ty_id, ty) in assoc_tys {
                    let assoc_ty = tys
                        .tys
                        .get_con(con)
                        .unwrap()
                        .assoc_tys
                        .get(&assoc_ty_id)
                        .unwrap()
                        .subst_qvars(&qvar_map)
                        .normalize(tys.tys.cons());

                    let expected_ty = ty.normalize(tys.tys.cons());

                    // TODO: We could show where the associated type is coming from in the error
                    // messages here, e.g. instead of "Unable to unify Str and I32", we could say
                    // "Unable to unify MyType.AssocTy (Str) and I32".
                    unification::unify(
                        &assoc_ty,
                        &expected_ty,
                        tys.tys.cons(),
                        var_gen,
                        level,
                        &loc,
                    );
                }
            }

            // TODO: Records can implement Debug, Eq, etc.
            Ty::QVar(_)
            | Ty::Var(_)
            | Ty::Anonymous { .. }
            | Ty::Fun { .. }
            | Ty::AssocTySelect { .. } => {
                remaining_preds.add(Pred {
                    ty_var,
                    trait_,
                    assoc_tys,
                    loc,
                });
            }
        }
    }

    remaining_preds
    */
}

fn resolve_all_preds(
    context: &Map<Id, QVar>,
    tys: &PgmTypes,
    preds: Set<Pred>,
    var_gen: &mut TyVarGen,
    level: u32,
) {
    let unresolved_preds = resolve_preds(context, tys, preds, var_gen, level);
    report_unresolved_preds(unresolved_preds, tys.tys.cons());
}

fn report_unresolved_preds(preds: Set<Pred>, cons: &ScopeMap<Id, TyCon>) {
    if preds.is_empty() {
        return;
    }

    for Pred {
        trait_,
        params,
        assoc_tys: _,
        loc,
    } in preds
    {
        eprintln!(
            "{}: Cannot resolve constraint {}[{}]",
            loc_display(&loc),
            trait_,
            params
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<String>>()
                .join(", "),
        );
    }

    panic!();
}

fn bind_type_params(
    params: &[(Id, QVar)],
    tys: &mut PgmTypes,
    loc: &ast::Loc,
) -> Map<SmolStr, Option<Map<SmolStr, Scheme>>> {
    let mut old_method_schemes: Map<Id, Option<Map<Id, Scheme>>> = Default::default();

    for (var, qvar) in params {
        old_method_schemes.insert(var.clone(), tys.method_schemes.remove(var));

        for (trait_, assoc_tys) in &qvar.bounds {
            // It should be checked when converting the bounds that the ty cons are bound and
            // traits.
            let trait_ty_con = tys.tys.get_con(trait_).unwrap();
            let trait_details = trait_ty_con.trait_details().unwrap();

            for (method_id, method) in &trait_details.methods {
                assert_eq!(trait_ty_con.ty_params.len(), 1);
                let trait_ty_param = &trait_ty_con.ty_params[0];
                let method_scheme =
                    method
                        .scheme
                        .subst(&trait_ty_param.0, &Ty::Con(var.clone()), loc);

                tys.method_schemes
                    .entry(var.clone())
                    .or_default()
                    .insert(method_id.clone(), method_scheme);
            }

            for (assoc_ty_id, ty) in assoc_tys {
                tys.tys
                    .get_con_mut(var)
                    .unwrap()
                    .assoc_tys
                    .insert(assoc_ty_id.clone(), ty.clone());
            }
        }
    }

    old_method_schemes
}

fn unbind_type_params(
    old_assoc_schemes: Map<Id, Option<Map<Id, Scheme>>>,
    assoc_schemes: &mut Map<Id, Map<Id, Scheme>>,
) {
    for (old_ty_con, old_assoc_schemes) in old_assoc_schemes {
        match old_assoc_schemes {
            Some(scheme) => {
                assoc_schemes.insert(old_ty_con, scheme);
            }
            None => {
                assoc_schemes.remove(&old_ty_con);
            }
        }
    }
}

fn fun_sig_ty_var_kinds(fun_sig: &ast::FunSig) -> Map<Id, Kind> {
    let mut kinds: Map<Id, Kind> = Default::default();
    for (_, param) in fun_sig.params.iter() {
        ty_var_kinds(&param.node, &mut kinds);
    }
    if let Some(exn) = &fun_sig.exceptions {
        ty_var_kinds(&exn.node, &mut kinds);
    }
    if let Some(ret) = &fun_sig.return_ty {
        ty_var_kinds(&ret.node, &mut kinds);
    }
    kinds
}

fn ty_var_kinds(ty: &ast::Type, kinds: &mut Map<Id, Kind>) {
    match ty {
        ast::Type::Named(ast::NamedType { name: _, args }) => {
            for arg in args {
                ty_var_kinds(&arg.node.1.node, kinds);
            }
        }

        ast::Type::Var(var) => {
            kinds.insert(var.clone(), Kind::Star);
        }

        ast::Type::Record { fields, extension } => {
            for field in fields {
                ty_var_kinds(&field.node, kinds);
            }
            if let Some(ext) = extension {
                kinds.insert(ext.clone(), Kind::Row(RecordOrVariant::Record));
            }
        }

        ast::Type::Variant { alts, extension } => {
            for ast::VariantAlt { con: _, fields } in alts {
                for field in fields {
                    ty_var_kinds(&field.node, kinds);
                }
            }
            if let Some(ext) = extension {
                kinds.insert(ext.clone(), Kind::Row(RecordOrVariant::Variant));
            }
        }

        ast::Type::Fn(ast::FnType {
            args,
            ret,
            exceptions,
        }) => {
            for arg in args {
                ty_var_kinds(&arg.node, kinds);
            }
            if let Some(ret) = ret {
                ty_var_kinds(&ret.node, kinds);
            }
            if let Some(exn) = exceptions {
                ty_var_kinds(&exn.node, kinds);
            }
        }
    }
}

fn constructor_fields_var_kinds(ty: &ast::ConstructorFields) -> Map<Id, Kind> {
    let mut kinds: Map<Id, Kind> = Default::default();
    constructor_fields_var_kinds_(ty, &mut kinds);
    kinds
}

fn constructor_fields_var_kinds_(ty: &ast::ConstructorFields, kinds: &mut Map<Id, Kind>) {
    match ty {
        ast::ConstructorFields::Empty => {}
        ast::ConstructorFields::Named(fields) => {
            for (_, field) in fields {
                ty_var_kinds(field, kinds);
            }
        }
        ast::ConstructorFields::Unnamed(fields) => {
            for field in fields {
                ty_var_kinds(field, kinds);
            }
        }
    }
}

fn constructor_decls_var_kinds(decls: &[ast::ConstructorDecl]) -> Map<Id, Kind> {
    let mut kinds: Map<Id, Kind> = Default::default();
    for decl in decls {
        constructor_fields_var_kinds_(&decl.fields, &mut kinds);
    }
    kinds
}
