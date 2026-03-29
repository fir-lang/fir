#![allow(clippy::mutable_key_type, clippy::for_kv_map)]

mod apply;
mod convert;
mod expr;
pub(crate) mod kind_inference;
mod normalization;
mod pat;
mod pat_coverage;
pub(crate) mod row_utils;
mod stmt;
mod traits;
mod ty;
mod ty_map;
mod unification;

pub use crate::utils::loc_display;
use convert::*;
use normalization::normalize_stmt;
use stmt::check_stmts;
use traits::*;
use ty::*;
pub use ty::{FunArgs, Kind, RecordOrVariant, Ty};
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
    pub top_schemes: HashMap<Id, Scheme>,

    /// Type schemes of associated functions.
    ///
    /// These include methods (associated functions with a `self` parameter).
    pub associated_fn_schemes: HashMap<Id, HashMap<Id, Scheme>>,

    /// Type schemes of methods.
    ///
    /// Maps method names to (type or trait name, type scheme) pairs.
    ///
    /// These are associated functions (so they're also in `associated_fn_schemes`) that take a
    /// `self` parameter.
    ///
    /// The first parameters of the function types here are the `self` types.
    ///
    /// Because these schemes are only used in method call syntax, the keys are not type names but
    /// method names. The values are type schemes of methods with the name.
    pub method_schemes: HashMap<Id, Vec<(Id, Scheme)>>,

    /// Type constructor details.
    pub tys: TyMap,
}

/// Type check a module.
///
/// Updates trait implementation blocks with the default implementations of missing methods.
///
/// Returns schemes of top-level functions, associated functions (includes trait methods), and
/// details of type constructors (`TyCon`).
pub(crate) fn check_module(module: &mut ast::Module, main: &str) -> PgmTypes {
    add_exception_types(module, main);
    kind_inference::add_missing_type_params(module);
    let mut tys = collect_types(module);
    let trait_env = collect_trait_env(module, &mut tys.tys);
    for decl in module {
        match &mut decl.node {
            ast::TopDecl::Import(_) => panic!(
                "{}: Import declaration in check_module",
                loc_display(&decl.loc)
            ),

            // Types and schemes added to `PgmTypes` by `collect_types`.
            ast::TopDecl::Type(_) | ast::TopDecl::Trait(_) => {}

            ast::TopDecl::Impl(impl_) => check_impl(impl_, &mut tys, &trait_env),

            ast::TopDecl::Fun(fun) => check_top_fun(fun, &mut tys, &trait_env),
        }
    }

    tys
}

pub(crate) fn check_main_type(tys: &PgmTypes, trait_env: &TraitEnv, main: &str) {
    let main_scheme = tys
        .top_schemes
        .get(main)
        .unwrap_or_else(|| panic!("Main function `{main}` is not defined."));

    if !main_scheme.quantified_vars.is_empty() || !main_scheme.preds.is_empty() {
        panic!("Main function `{main}` can't have quantified variables and predicates.");
    }

    unification::unify(
        &main_scheme.ty,
        &Ty::Fun {
            args: FunArgs::Positional { args: vec![] },
            ret: Box::new(Ty::unit()),
            exceptions: Some(Box::new(Ty::empty_variant())),
        },
        tys.tys.cons(),
        trait_env,
        &UVarGen::default(),
        0,
        &main_scheme.loc,
        &[],
        &mut vec![],
    );
}

/// Add exception types to functions without one.
fn add_exception_types(module: &mut ast::Module, main: &str) {
    for decl in module {
        match &mut decl.node {
            ast::TopDecl::Fun(ast::L { node: fun, loc }) => {
                if fun.sig.exceptions.is_none() {
                    if fun.name.node == main {
                        fun.sig.exceptions = Some(ast::L {
                            node: ast::Type::Variant {
                                alts: Default::default(),
                                extension: None,
                                is_row: false,
                            },
                            loc: loc.clone(),
                        });
                    } else {
                        fun.sig.exceptions = Some(exn_type(
                            fun.name.loc.module.clone(),
                            fun.name.loc.line_start,
                        ));
                    }
                }
            }

            ast::TopDecl::Trait(ast::L { node, .. }) => {
                for item in &mut node.items {
                    match item {
                        ast::TraitDeclItem::Type(_) => {}
                        ast::TraitDeclItem::Fun(fun) => {
                            if fun.node.sig.exceptions.is_none() {
                                fun.node.sig.exceptions =
                                    Some(exn_type(fun.loc.module.clone(), fun.loc.line_start));
                            }
                        }
                    }
                }
            }

            ast::TopDecl::Impl(ast::L { node, .. }) => {
                for item in &mut node.items {
                    match item {
                        ast::ImplDeclItem::Type { .. } => {}
                        ast::ImplDeclItem::Fun(fun) => {
                            if fun.node.sig.exceptions.is_none() {
                                fun.node.sig.exceptions =
                                    Some(exn_type(fun.loc.module.clone(), fun.loc.line_start));
                            }
                        }
                    }
                }
            }

            ast::TopDecl::Import(_) | ast::TopDecl::Type(_) => {}
        }
    }
}

// The default exception type: `?exn`.
fn exn_type(module: std::rc::Rc<str>, line: u16) -> ast::L<ast::Type> {
    ast::L {
        node: ast::Type::Var(EXN_QVAR_ID),
        loc: ast::Loc {
            module,
            line_start: line,
            col_start: 0,
            byte_offset_start: 0,
            line_end: line,
            col_end: 0,
            byte_offset_end: 0,
        },
    }
}

/// Type checking state for a single function (top-level, associated, or method).
struct TcFunState<'a> {
    /// Term environment.
    env: &'a mut ScopeMap<Id, Ty>,

    /// Whole program trait environment. Used to resolve closure predicate.s
    trait_env: &'a TraitEnv,

    /// Type environment.
    tys: &'a mut PgmTypes,

    /// Unification variable generator.
    var_gen: &'a UVarGen,

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
    ///
    /// This is a `Vec` instead of `Set`: `Pred` stores the location of the expression that
    /// generated the predicate, and because the type checker visits an expression only once, no two
    /// `Pred`s will have the same `Loc`. So this will never have duplicates.
    preds: &'a mut Vec<Pred>,

    /// Assumptions in scope. These come from function contexts: `f[<context>](<args>): <body>`.
    assumps: &'a Vec<Pred>,

    /// Local counter for generating new temporaries.
    local_gen: u32,
}

const EXN_QVAR_ID: Id = SmolStr::new_static("?exn");

/// Collect type constructors (traits and data) and type schemes (top-level, associated, traits) of
/// the program.
///
/// Does not type check the code, only collects types and type schemes.
fn collect_types(module: &mut ast::Module) -> PgmTypes {
    let mut tys = collect_cons(module);
    let (top_schemes, associated_fn_schemes, method_schemes) = collect_schemes(module, &mut tys);
    check_value_type_sizes(tys.cons());
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
                // Type synonyms are handled separately after this pass.
                if matches!(ty_decl.node.rhs, Some(ast::TypeDeclRhs::Synonym(_))) {
                    continue;
                }
                assert_eq!(
                    ty_decl.node.type_params.len(),
                    ty_decl.node.type_param_kinds.len(),
                    "{}: Type parameter list and kind list don't match",
                    loc_display(&decl.loc),
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
                        details: TyConDetails::Type(TypeDetails {
                            cons: Default::default(),
                            sum: true,
                            value: ty_decl.node.value,
                        }),
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
                            assoc_tys: Default::default(),
                        }),
                    },
                );
            }

            ast::TopDecl::Import(_) | ast::TopDecl::Fun(_) | ast::TopDecl::Impl(_) => continue,
        }
    }

    // Convert and register type synonyms. This must happen after all type constructors are
    // registered (so synonym RHSs can reference them) and before fields/methods are processed (so
    // field types can reference synonyms).
    //
    // Synonyms can reference each other in any order, so we first collect all synonym definitions,
    // then resolve each one on demand with cycle detection.
    {
        let mut synonym_asts: HashMap<Id, &ast::L<ast::Type>> = Default::default();
        for decl in module.iter() {
            if let ast::TopDecl::Type(ty_decl) = &decl.node
                && let Some(ast::TypeDeclRhs::Synonym(rhs_ty)) = &ty_decl.node.rhs
            {
                synonym_asts.insert(ty_decl.node.name.clone(), rhs_ty);
            }
        }

        let mut resolving: HashSet<Id> = Default::default();
        let names: Vec<Id> = synonym_asts.keys().cloned().collect();
        for name in &names {
            resolve_synonym(name, &synonym_asts, &mut resolving, &mut tys);
        }
    }

    // Add fields and methods.
    // This is where we start converting AST types to type checking types, so the ty con map should
    // be populated at this point.
    for decl in module.iter() {
        match &decl.node {
            ast::TopDecl::Type(ty_decl) => {
                // Type synonyms already handled above.
                if matches!(ty_decl.node.rhs, Some(ast::TypeDeclRhs::Synonym(_))) {
                    continue;
                }

                let details = match &ty_decl.node.rhs {
                    Some(rhs) => match rhs {
                        ast::TypeDeclRhs::Sum { .. } => TyConDetails::Type(TypeDetails {
                            cons: Default::default(),
                            sum: true,
                            value: ty_decl.node.value,
                        }),

                        ast::TypeDeclRhs::Product(_fields) => TyConDetails::Type(TypeDetails {
                            cons: Default::default(),
                            sum: false,
                            value: ty_decl.node.value,
                        }),

                        ast::TypeDeclRhs::Synonym(_) => unreachable!(),
                    },

                    None => TyConDetails::Type(TypeDetails {
                        cons: Default::default(),
                        sum: true,
                        value: ty_decl.node.value,
                    }),
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

                let _trait_context: Vec<Pred> =
                    convert_and_bind_context(&mut tys, &trait_context_ast, TyVarConversion::ToQVar);

                let mut methods: HashMap<Id, TraitMethod> = HashMap::with_capacity_and_hasher(
                    trait_decl.node.items.len(),
                    Default::default(),
                );

                let mut assoc_tys: HashSet<Id> = Default::default();

                for item in &trait_decl.node.items {
                    match item {
                        ast::TraitDeclItem::Type(assoc_ty) => {
                            let new = assoc_tys.insert(assoc_ty.node.clone());
                            if !new {
                                panic!(
                                    "{}: Associated type {} declared multiple times",
                                    loc_display(&assoc_ty.loc),
                                    assoc_ty.node
                                );
                            }
                            // Add a type synonym so that `Item` resolves to
                            // `TraitName[params...].Item` within the trait body.
                            let trait_ty = {
                                let trait_name = trait_decl.node.name.node.clone();
                                let args: Vec<Ty> = trait_decl
                                    .node
                                    .type_params
                                    .iter()
                                    .zip(trait_decl.node.type_param_kinds.iter())
                                    .map(|(p, k)| Ty::QVar(p.node.clone(), *k))
                                    .collect();
                                if args.is_empty() {
                                    Ty::Con(trait_name, Kind::Star)
                                } else {
                                    Ty::App(trait_name, args, Kind::Star)
                                }
                            };
                            tys.insert_synonym(
                                assoc_ty.node.clone(),
                                Ty::AssocTySelect {
                                    ty: Box::new(trait_ty),
                                    assoc_ty: assoc_ty.node.clone(),
                                },
                            );
                        }

                        ast::TraitDeclItem::Fun(fun) => {
                            // New scope for function context.
                            tys.enter_scope();

                            let fun_preds: Vec<Pred> = convert_and_bind_context(
                                &mut tys,
                                &fun.node.sig.context,
                                TyVarConversion::ToQVar,
                            );

                            let mut arg_tys: Vec<Ty> = fun
                                .node
                                .sig
                                .params
                                .iter()
                                .map(|(_name, ty)| {
                                    let ty = ty.as_ref().unwrap();
                                    convert_ast_ty(&tys, &ty.node, &ty.loc)
                                })
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
                                args: FunArgs::Positional { args: arg_tys },
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

                            methods.insert(fun.node.name.node.clone(), {
                                TraitMethod {
                                    scheme,
                                    fun_decl: fun.clone(),
                                }
                            });
                        }
                    }
                }

                let ty_con = tys.get_con_mut(&trait_decl.node.name.node).unwrap();
                ty_con.details = TyConDetails::Trait(TraitDetails { methods, assoc_tys });

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

        // Check that the trait in the impl block is really a trait.
        if !tys
            .get_con(trait_con_id)
            .unwrap_or_else(|| panic!("{}: Unknown trait {}", loc_display(&decl.loc), trait_con_id))
            .is_trait()
        {
            panic!(
                "{}: {} in impl declararation is not a trait",
                loc_display(&decl.loc),
                trait_con_id
            );
        }

        // Check that the number of type parameters in the trait matches number of arguments in the
        // impl.
        // TODO: We should also check the kinds here.
        let trait_arity = tys.get_con(trait_con_id).unwrap().arity();
        if trait_arity as usize != impl_decl.tys.len() {
            panic!(
                "{}: Trait {} takes {} type arguments, but impl passes {}",
                loc_display(&decl.loc),
                trait_con_id,
                trait_arity,
                impl_decl.tys.len()
            );
        }

        // New scope for the context.
        assert_eq!(tys.len_scopes(), 1);
        tys.enter_scope();

        let _impl_context =
            convert_and_bind_context(&mut tys, &impl_decl.context, TyVarConversion::ToQVar);

        let trait_ty_con = tys.get_con_mut(trait_con_id).unwrap(); // checked above
        let trait_type_params = &trait_ty_con.ty_params;
        let trait_methods = match &mut trait_ty_con.details {
            TyConDetails::Trait(TraitDetails {
                methods,
                assoc_tys: _,
            }) => methods,
            TyConDetails::Type { .. } => {
                panic!() // checked above
            }
        };

        for (trait_method_id, trait_method_decl) in trait_methods {
            if trait_method_decl.fun_decl.node.body.is_none() {
                continue;
            }

            if impl_decl.items.iter().any(|item| match item {
                ast::ImplDeclItem::Type {
                    assoc_ty: _,
                    rhs: _,
                } => false,
                ast::ImplDeclItem::Fun(fun) => &fun.node.name.node == trait_method_id,
            }) {
                continue;
            }

            let mut impl_fun_decl = trait_method_decl.fun_decl.clone();

            // Rename copied function's type parameters so that they won't be shadowed by the impl's
            // type parameters.
            let mut new_type_params: Vec<(Id, Kind)> =
                Vec::with_capacity(impl_fun_decl.node.sig.context.type_params.len());

            let renaming_substs: HashMap<Id, ast::Type> = impl_fun_decl
                .node
                .sig
                .context
                .type_params
                .iter()
                .map(|(ty_param, kind)| {
                    let new_param = SmolStr::new(format!("{}$copy", ty_param));
                    new_type_params.push((new_param.clone(), *kind));
                    (ty_param.clone(), ast::Type::Var(new_param))
                })
                .collect();

            impl_fun_decl.node.sig.context.type_params = new_type_params;
            impl_fun_decl.node.sig.subst_ty_ids(&renaming_substs);

            // Map type parameters of the trait to the impl types.
            let substs: HashMap<Id, ast::Type> = trait_type_params
                .iter()
                .map(|(param, _param_kind)| param.clone())
                .zip(impl_decl.tys.iter().map(|ty| ty.node.clone()))
                .collect();

            if let Some(body) = &mut impl_fun_decl.node.body {
                for stmt in body {
                    stmt.node.subst_ty_ids(&renaming_substs);
                    stmt.node.subst_ty_ids(&substs);
                }
            }

            impl_fun_decl.node.sig.subst_ty_ids(&substs);

            impl_fun_decl.loc = decl.loc.clone();

            impl_decl.items.push(ast::ImplDeclItem::Fun(impl_fun_decl));
        }

        tys.exit_scope();
        assert_eq!(tys.len_scopes(), 1);
    }

    assert_eq!(tys.len_scopes(), 1);
    tys
}

/// Resolve a type synonym by converting its RHS. If the RHS references another synonym, resolve
/// that one first (recursively). Detects cycles via the `resolving` set.
fn resolve_synonym(
    name: &Id,
    synonym_asts: &HashMap<Id, &ast::L<ast::Type>>,
    resolving: &mut HashSet<Id>,
    tys: &mut TyMap,
) {
    // Already resolved in a previous call.
    if tys.get_synonym(name).is_some() {
        return;
    }

    if !resolving.insert(name.clone()) {
        let cycle: Vec<&str> = resolving.iter().map(|id| id.as_str()).collect();
        panic!("Type synonym cycle detected: {}", cycle.join(", "));
    }

    let rhs_ty = synonym_asts.get(name).unwrap();

    // Resolve synonyms in the RHS.
    resolve_synonym_deps(&rhs_ty.node, synonym_asts, resolving, tys);

    let converted = convert_ast_ty(tys, &rhs_ty.node, &rhs_ty.loc);
    tys.insert_synonym(name.clone(), converted);

    resolving.remove(name);
}

/// Recursively resolve any synonym dependencies in an AST type.
fn resolve_synonym_deps(
    ty: &ast::Type,
    synonym_asts: &HashMap<Id, &ast::L<ast::Type>>,
    resolving: &mut HashSet<Id>,
    tys: &mut TyMap,
) {
    match ty {
        ast::Type::Named(ast::NamedType { name, args }) => {
            if args.is_empty() && synonym_asts.contains_key(name) {
                resolve_synonym(name, synonym_asts, resolving, tys);
            }
            for arg in args {
                resolve_synonym_deps(&arg.node, synonym_asts, resolving, tys);
            }
        }
        ast::Type::Var(_) => {}
        ast::Type::Record { fields, .. } => {
            for (_, field_ty) in fields {
                resolve_synonym_deps(field_ty, synonym_asts, resolving, tys);
            }
        }
        ast::Type::Variant { alts, .. } => {
            for alt in alts {
                for arg in &alt.args {
                    resolve_synonym_deps(&arg.node, synonym_asts, resolving, tys);
                }
            }
        }
        ast::Type::Fn(ast::FnType {
            args,
            ret,
            exceptions,
        }) => {
            for arg in args {
                resolve_synonym_deps(&arg.node, synonym_asts, resolving, tys);
            }
            if let Some(ret) = ret {
                resolve_synonym_deps(&ret.node, synonym_asts, resolving, tys);
            }
            if let Some(exn) = exceptions {
                resolve_synonym_deps(&exn.node, synonym_asts, resolving, tys);
            }
        }
        ast::Type::AssocTySelect { ty: inner, .. } => {
            resolve_synonym_deps(&inner.node, synonym_asts, resolving, tys);
        }
    }
}

fn check_value_type_sizes(ty_cons: &HashMap<Id, TyCon>) {
    for ty_con in ty_cons.values() {
        let mut visited: HashSet<Id> = Default::default();
        let ty_args: Vec<Ty> = ty_con
            .ty_params
            .iter()
            .map(|(name, kind)| Ty::Con(SmolStr::new(format!("#{}", name)), *kind))
            .collect();
        if visit_ty_con(ty_con, &ty_args, ty_cons, &mut visited) {
            panic!(
                "Value type {} has infinite size due to recursion",
                ty_con.id
            );
        }
    }
}

/// Returns whether we've detected a cycle.
fn visit_ty_con(
    ty_con: &TyCon,
    ty_args: &[Ty],
    ty_cons: &HashMap<Id, TyCon>,
    visited: &mut HashSet<Id>,
) -> bool {
    let ty_con_details = match &ty_con.details {
        TyConDetails::Trait(_) => return false,
        TyConDetails::Type(details) => details,
    };

    if !ty_con_details.value {
        return false;
    }

    if !visited.insert(ty_con.id.clone()) {
        return true;
    }

    for (_con_name, con_scheme) in ty_con_details.cons.iter() {
        let con_ty = con_scheme.instantiate_with_tys(ty_args, &mut vec![], &ast::Loc::dummy());

        let con_args = match con_ty {
            Ty::Fun { args, .. } => args,
            _ => continue,
        };

        let mut tys: Vec<&Ty> = match &con_args {
            FunArgs::Positional { args } => args.iter().collect(),
            FunArgs::Named { args, .. } => args.values().collect(),
        };

        while let Some(ty) = tys.pop() {
            match ty {
                Ty::Con(con, _kind) => {
                    if let Some(ty_con) = ty_cons.get(con)
                        && visit_ty_con(ty_con, &[], ty_cons, visited)
                    {
                        return true;
                    }
                }

                Ty::App(con, args, _kind) => {
                    if visit_ty_con(ty_cons.get(con).unwrap(), args, ty_cons, visited) {
                        return true;
                    }
                }

                Ty::Anonymous {
                    labels,
                    extension: _,
                    record_or_variant: _,
                    is_row: _,
                } => {
                    for label_ty in labels.values() {
                        tys.push(label_ty);
                    }
                }

                Ty::Fun { .. } => {}

                Ty::RVar(_, _) | Ty::QVar(_, _) | Ty::UVar(_) | Ty::AssocTySelect { .. } => {
                    panic!()
                }
            }
        }
    }

    false
}

// `tys` is `mut` to be able to update it with associated types when checking traits.
fn collect_schemes(
    module: &ast::Module,
    tys: &mut TyMap,
) -> (
    HashMap<Id, Scheme>,              // top schemes
    HashMap<Id, HashMap<Id, Scheme>>, // associated fn schemes
    HashMap<Id, Vec<(Id, Scheme)>>,   // method schemes (method name -> type name -> scheme)
) {
    let mut top_schemes: HashMap<Id, Scheme> = Default::default();
    let mut associated_fn_schemes: HashMap<Id, HashMap<Id, Scheme>> = Default::default();
    let mut method_schemes: HashMap<Id, Vec<(Id, Scheme)>> = Default::default();

    // Unique variable generator, used in substitutions to rename domain variables before
    // substitution to avoid capturing.
    // TODO: This should be generalized and used in all substitutions.
    let mut uniq_gen: u32 = 0;

    for decl in module {
        // New scope for type and function contexts.
        assert_eq!(tys.len_scopes(), 1);
        tys.enter_scope();

        match &decl.node {
            ast::TopDecl::Trait(trait_decl) => {
                /*
                trait ToStr[t]:
                    toStr(self: t) Str
                ==>
                ToStr.toStr[ToStr[t]](self: t) Str

                trait Iterator[iter, item]:
                    next(self: Iterator[iter, item]) Option[item]
                ==>
                Iterator.next[Iterator[iter, item]](self: Iterator[iter, item]) Option[item]
                */

                assert_eq!(
                    trait_decl.node.type_params.len(),
                    trait_decl.node.type_param_kinds.len()
                );

                // Note: this needs to be a `Vec` instead of a `Map` as we need to add trait context
                // before the function context in the method type schemes, and type parameters in
                // the trait context need to be in the same order as the trait declaration.
                let trait_quantified_vars: Vec<(Id, Kind)> = trait_decl
                    .node
                    .type_params
                    .iter()
                    .map(|p| p.node.clone())
                    .zip(trait_decl.node.type_param_kinds.iter().cloned())
                    .collect();

                let trait_pred: ast::L<ast::Pred> = ast::L {
                    loc: trait_decl.loc.clone(),
                    node: ast::Pred::App(ast::NamedType {
                        name: trait_decl.node.name.node.clone(),
                        args: trait_decl
                            .node
                            .type_params
                            .iter()
                            .map(|param| param.map_as_ref(|param| ast::Type::Var(param.clone())))
                            .collect(),
                    }),
                };

                for item in &trait_decl.node.items {
                    let fun = match item {
                        ast::TraitDeclItem::Type(_) => continue,
                        ast::TraitDeclItem::Fun(fun) => fun,
                    };

                    // Add trait type parameters and predicate to the function context before
                    // converting.
                    // Note: This needs to be a `Vec` instead of `Map`. See the comments around
                    // `trait_quantified_vars`.
                    let mut fun_type_params = trait_quantified_vars.clone();
                    fun_type_params.extend(fun.node.sig.context.type_params.clone());

                    let mut fun_preds: Vec<ast::L<ast::Pred>> = vec![trait_pred.clone()];
                    fun_preds.extend(fun.node.sig.context.preds.clone());

                    let context = ast::Context {
                        type_params: fun_type_params,
                        preds: fun_preds,
                    };

                    // TODO: Checking is the same as top-level functions, maybe move the code into a
                    // function and reuse.
                    let fun_preds: Vec<Pred> =
                        convert_and_bind_context(tys, &context, TyVarConversion::ToQVar);

                    // Add type synonyms for associated types so that e.g. `Item` resolves to
                    // `TraitName[params...].Item` within method signatures.
                    for trait_item in &trait_decl.node.items {
                        if let ast::TraitDeclItem::Type(assoc_ty) = trait_item {
                            let trait_ty = {
                                let trait_name = trait_decl.node.name.node.clone();
                                let args: Vec<Ty> = trait_decl
                                    .node
                                    .type_params
                                    .iter()
                                    .zip(trait_decl.node.type_param_kinds.iter())
                                    .map(|(p, k)| Ty::QVar(p.node.clone(), *k))
                                    .collect();
                                if args.is_empty() {
                                    Ty::Con(trait_name, Kind::Star)
                                } else {
                                    Ty::App(trait_name, args, Kind::Star)
                                }
                            };
                            tys.insert_synonym(
                                assoc_ty.node.clone(),
                                Ty::AssocTySelect {
                                    ty: Box::new(trait_ty),
                                    assoc_ty: assoc_ty.node.clone(),
                                },
                            );
                        }
                    }

                    let mut arg_tys: Vec<Ty> = fun
                        .node
                        .sig
                        .params
                        .iter()
                        .map(|(_name, ty)| {
                            let ty = ty.as_ref().unwrap();
                            convert_ast_ty(tys, &ty.node, &ty.loc)
                        })
                        .collect();

                    match &fun.node.sig.self_ {
                        ast::SelfParam::No => {}
                        ast::SelfParam::Implicit => {
                            panic!(
                                "{}: Trait method self parameters should have explicit self type",
                                loc_display(&fun.loc)
                            );
                        }
                        ast::SelfParam::Explicit(ty) => {
                            arg_tys.insert(0, convert_ast_ty(tys, &ty.node, &ty.loc));
                        }
                    }

                    let ret_ty: Ty = match &fun.node.sig.return_ty {
                        Some(ret_ty) => convert_ast_ty(tys, &ret_ty.node, &ret_ty.loc),
                        None => Ty::unit(),
                    };

                    let exceptions = match &fun.node.sig.exceptions {
                        Some(ty) => convert_ast_ty(tys, &ty.node, &ty.loc),
                        None => panic!(),
                    };

                    let fun_ty = Ty::Fun {
                        args: FunArgs::Positional { args: arg_tys },
                        ret: Box::new(ret_ty),
                        exceptions: Some(Box::new(exceptions)),
                    };

                    let scheme = Scheme {
                        quantified_vars: context.type_params.into_iter().collect(),
                        preds: fun_preds,
                        ty: fun_ty,
                        loc: fun.loc.clone(),
                    };

                    if !matches!(fun.node.sig.self_, ast::SelfParam::No) {
                        method_schemes
                            .entry(fun.node.name.node.clone())
                            .or_default()
                            .push((trait_decl.node.name.node.clone(), scheme.clone()));
                    }

                    associated_fn_schemes
                        .entry(trait_decl.node.name.node.clone())
                        .or_default()
                        .insert(fun.node.name.node.clone(), scheme);
                }
            }

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
                // Check that `parent_ty` exists.
                if let Some(parent_ty) = parent_ty
                    && tys.get_con(&parent_ty.node).is_none()
                {
                    panic!(
                        "{}: Unknown type {}",
                        loc_display(&decl.loc),
                        &parent_ty.node
                    );
                }

                let fun_preds: Vec<Pred> =
                    convert_and_bind_context(tys, &sig.context, TyVarConversion::ToQVar);

                let mut arg_tys: Vec<Ty> = sig
                    .params
                    .iter()
                    .map(|(_name, ty)| {
                        let ty = ty.as_ref().unwrap();
                        convert_ast_ty(tys, &ty.node, &ty.loc)
                    })
                    .collect();

                match &sig.self_ {
                    ast::SelfParam::No => {}
                    ast::SelfParam::Implicit => {
                        // The parent type should have no type arguments.
                        match parent_ty {
                            Some(parent_ty) => {
                                // We checked above that the parent type exists.
                                let parent_ty_con = tys.get_con(&parent_ty.node).unwrap();
                                if !parent_ty_con.ty_params.is_empty() {
                                    panic!(
                                        "{}: Can't infer `self` type as the parent type {} has type parameters",
                                        loc_display(&decl.loc),
                                        &parent_ty.node
                                    );
                                }
                                arg_tys.insert(0, Ty::Con(parent_ty_con.id.clone(), Kind::Star));
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
                    args: FunArgs::Positional { args: arg_tys },
                    ret: Box::new(ret_ty),
                    exceptions: Some(Box::new(exceptions)),
                };

                let scheme = Scheme {
                    quantified_vars: sig.context.type_params.to_vec(),
                    preds: fun_preds,
                    ty: fun_ty,
                    loc: loc.clone(),
                };

                match parent_ty {
                    Some(parent_ty) => {
                        match sig.self_ {
                            ast::SelfParam::No => {}
                            ast::SelfParam::Implicit | ast::SelfParam::Explicit(_) => {
                                method_schemes
                                    .entry(name.node.clone())
                                    .or_default()
                                    .push((parent_ty.node.clone(), scheme.clone()));
                            }
                        }

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
                    Some(ast::TypeDeclRhs::Synonym(_)) | None => {
                        tys.exit_scope();
                        continue;
                    }
                    Some(rhs) => rhs,
                };

                // Bind type parameters in the context for constructor schemes.
                assert_eq!(
                    ty_decl.node.type_params.len(),
                    ty_decl.node.type_param_kinds.len()
                );
                for (ty_var, ty_var_kind) in ty_decl
                    .node
                    .type_params
                    .iter()
                    .zip(ty_decl.node.type_param_kinds.iter())
                {
                    tys.insert_var(ty_var.clone(), Ty::QVar(ty_var.clone(), *ty_var_kind));
                }

                // Return type of constructors.
                let ret = if ty_decl.node.type_params.is_empty() {
                    Ty::Con(ty_decl.node.name.clone(), Kind::Star)
                } else {
                    Ty::App(
                        ty_decl.node.name.clone(),
                        ty_decl
                            .node
                            .type_params
                            .iter()
                            .zip(ty_decl.node.type_param_kinds.iter())
                            .map(|(ty_var, ty_var_kind)| Ty::QVar(ty_var.clone(), *ty_var_kind))
                            .collect(),
                        Kind::Star,
                    )
                };

                match rhs {
                    ast::TypeDeclRhs::Sum { cons, extension } => {
                        if extension.is_some() {
                            panic!(
                                "{}: Extensible sums not fully supported yet",
                                loc_display(&ty_decl.loc)
                            );
                        }
                        for con in cons {
                            let fields = &con.fields;
                            let ty = match convert_fields(tys, fields) {
                                None => ret.clone(),
                                Some(args) => Ty::Fun {
                                    args,
                                    ret: Box::new(ret.clone()),
                                    exceptions: None,
                                },
                            };
                            let scheme = Scheme {
                                quantified_vars: ty_decl
                                    .node
                                    .type_params
                                    .iter()
                                    .cloned()
                                    .zip(ty_decl.node.type_param_kinds.iter().cloned())
                                    .collect(),
                                preds: Default::default(),
                                ty,
                                loc: ty_decl.loc.clone(), // TODO: use con loc
                            };
                            let old = tys
                                .get_con_mut(&ty_decl.node.name)
                                .unwrap()
                                .details
                                .as_type_mut()
                                .cons
                                .insert(con.name.clone(), scheme.clone());
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
                        let ty = match convert_fields(tys, fields) {
                            None => ret,
                            Some(args) => Ty::Fun {
                                args,
                                ret: Box::new(ret.clone()),
                                exceptions: None,
                            },
                        };
                        let scheme = Scheme {
                            quantified_vars: ty_decl
                                .node
                                .type_params
                                .iter()
                                .cloned()
                                .zip(ty_decl.node.type_param_kinds.iter().cloned())
                                .collect(),
                            preds: Default::default(),
                            ty,
                            loc: ty_decl.loc.clone(), // TODO: use con loc
                        };
                        let old = tys
                            .get_con_mut(&ty_decl.node.name)
                            .unwrap()
                            .details
                            .as_type_mut()
                            .cons
                            .insert(ty_decl.node.name.clone(), scheme.clone());
                        if old.is_some() {
                            panic!(
                                "{}: Constructor {} is defined multiple times",
                                loc_display(&ty_decl.loc), // TODO: use con loc
                                ty_decl.node.name,
                            );
                        }
                    }

                    ast::TypeDeclRhs::Synonym(_) => {
                        // Synonyms are skipped above.
                        unreachable!()
                    }
                }
            }

            ast::TopDecl::Impl(impl_decl) => {
                // Default methods are already copied to impls. Check that impl method signatures
                // match the trait method signatures.
                let _impl_assumps =
                    convert_and_bind_context(tys, &impl_decl.node.context, TyVarConversion::ToQVar);

                // Add type synonyms for associated types, mapping to
                // `TraitName[args...].AssocTyName` so that both trait and impl sides produce the
                // same `AssocTySelect` structure for `eq_modulo_alpha`.
                let impl_trait_ty = {
                    let trait_name = impl_decl.node.trait_.node.clone();
                    let args: Vec<Ty> = impl_decl
                        .node
                        .tys
                        .iter()
                        .map(|ty| convert_ast_ty(tys, &ty.node, &ty.loc))
                        .collect();
                    if args.is_empty() {
                        Ty::Con(trait_name, Kind::Star)
                    } else {
                        Ty::App(trait_name, args, Kind::Star)
                    }
                };
                for item in &impl_decl.node.items {
                    if let ast::ImplDeclItem::Type { assoc_ty, .. } = item {
                        tys.insert_synonym(
                            assoc_ty.node.clone(),
                            Ty::AssocTySelect {
                                ty: Box::new(impl_trait_ty.clone()),
                                assoc_ty: assoc_ty.node.clone(),
                            },
                        );
                    }
                }

                for item in &impl_decl.node.items {
                    let fun = match item {
                        ast::ImplDeclItem::Type { .. } => continue,
                        ast::ImplDeclItem::Fun(fun) => fun,
                    };

                    let sig = &fun.node.sig;

                    let fun_assumps =
                        convert_and_bind_context(tys, &sig.context, TyVarConversion::ToQVar);

                    let mut arg_tys: Vec<Ty> = sig
                        .params
                        .iter()
                        .map(|(_name, ty)| {
                            let ty = ty.as_ref().unwrap();
                            convert_ast_ty(tys, &ty.node, &ty.loc)
                        })
                        .collect();

                    match &sig.self_ {
                        ast::SelfParam::No => {}
                        ast::SelfParam::Implicit => panic!(
                            "{}: Impl method with implicit self type",
                            loc_display(&fun.loc)
                        ),
                        ast::SelfParam::Explicit(ty) => {
                            let ty = convert_ast_ty(tys, &ty.node, &ty.loc);
                            arg_tys.insert(0, ty);
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
                        args: FunArgs::Positional { args: arg_tys },
                        ret: Box::new(ret_ty),
                        exceptions: Some(Box::new(exceptions)),
                    };

                    let impl_fun_scheme = Scheme {
                        quantified_vars: fun.node.sig.context.type_params.clone(),
                        preds: fun_assumps.to_vec(),
                        ty: fun_ty,
                        loc: fun.loc.clone(),
                    };

                    let trait_ty_con =
                        tys.get_con(&impl_decl.node.trait_.node).unwrap_or_else(|| {
                            panic!(
                                "{}: Unknown trait {}",
                                loc_display(&impl_decl.loc),
                                &impl_decl.node.trait_.node
                            )
                        });

                    let trait_fun_scheme0 = &trait_ty_con
                        .trait_details()
                        .unwrap_or_else(|| {
                            panic!(
                                "{}: {} is not a trait",
                                loc_display(&impl_decl.loc),
                                &impl_decl.node.trait_.node
                            )
                        })
                        .methods
                        .get(&fun.node.name.node)
                        .unwrap_or_else(|| {
                            panic!(
                                "{}: Trait {} does not have a method named {}",
                                loc_display(&impl_decl.loc),
                                &impl_decl.node.trait_.node,
                                &fun.node.name.node
                            )
                        })
                        .scheme;

                    let mut trait_fun_scheme = trait_fun_scheme0.rename_qvars(uniq_gen);

                    let uniq = uniq_gen;
                    uniq_gen += 1;

                    // Substitute trait arguments. Add free variables of the arguments to the
                    // context.

                    let mut arg_fvs: OrderMap<Id, Option<Kind>> = Default::default();

                    for ((ty_param, _), ty_arg) in
                        trait_ty_con.ty_params.iter().zip(impl_decl.node.tys.iter())
                    {
                        let ty_param_renamed = rename_domain_var(ty_param, uniq);
                        kind_inference::collect_tvs(&ty_arg.node, &ty_arg.loc, &mut arg_fvs);
                        let ty_arg = convert_ast_ty(tys, &ty_arg.node, &ty_arg.loc);
                        trait_fun_scheme = trait_fun_scheme.subst(&ty_param_renamed, &ty_arg);
                    }

                    if !trait_fun_scheme.eq_modulo_alpha(tys.cons(), &impl_fun_scheme, &fun.loc) {
                        panic!(
                            "{}: Trait method implementation of {} does not match the trait method type
                                Trait method type:          {}
                                Implementation method type: {}",
                            loc_display(&fun.loc),
                            &fun.node.name.node,
                            trait_fun_scheme,
                            impl_fun_scheme
                        );
                    }
                }
            }

            ast::TopDecl::Import(_) => {
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
fn check_top_fun(fun: &mut ast::L<ast::FunDecl>, tys: &mut PgmTypes, trait_env: &TraitEnv) {
    let var_gen = UVarGen::default();
    let mut env: ScopeMap<Id, Ty> = ScopeMap::default();

    assert_eq!(tys.tys.len_scopes(), 1);
    tys.tys.enter_scope();

    // The predicates that we assume to hold in the function body.
    let assumps =
        convert_and_bind_context(&mut tys.tys, &fun.node.sig.context, TyVarConversion::ToRVar);

    // TODO: This code is the same as collect_scheme's, maybe get arg and return types from the
    // scheme?
    match &fun.node.sig.self_ {
        ast::SelfParam::No => {}
        ast::SelfParam::Implicit => {
            // The parent type should have no type arguments.
            match &fun.node.parent_ty {
                Some(parent_ty) => {
                    let parent_ty_con = tys.tys.get_con(&parent_ty.node).unwrap_or_else(|| {
                        panic!(
                            "{}: Unknown type {}",
                            loc_display(&fun.loc),
                            &parent_ty.node
                        )
                    });
                    if !parent_ty_con.ty_params.is_empty() {
                        panic!(
                            "{}: Can't infer `self` type as the parent type {} has type parameters",
                            loc_display(&fun.loc),
                            &parent_ty.node
                        );
                    }
                    env.insert(
                        SmolStr::new_static("self"),
                        Ty::Con(parent_ty_con.id.clone(), Kind::Star),
                    );
                }
                None => panic!(
                    "{}: Function with `self` type needs to have to be an associated function",
                    loc_display(&fun.loc)
                ),
            }
        }
        ast::SelfParam::Explicit(ty) => {
            env.insert(
                SmolStr::new_static("self"),
                convert_ast_ty(&tys.tys, &ty.node, &ty.loc),
            );
        }
    }

    for (param_name, param_ty) in &fun.node.sig.params {
        let param_ty = param_ty.as_ref().unwrap();
        env.insert(
            param_name.clone(),
            convert_ast_ty(&tys.tys, &param_ty.node, &fun.loc),
        );
    }

    let ret_ty = match &fun.node.sig.return_ty {
        Some(ty) => convert_ast_ty(&tys.tys, &ty.node, &ty.loc),
        None => Ty::unit(),
    };
    let mut preds: Vec<Pred> = Default::default();

    let exceptions = match &fun.node.sig.exceptions {
        Some(exc) => convert_ast_ty(&tys.tys, &exc.node, &exc.loc),
        None => panic!(),
    };

    let mut tc_state = TcFunState {
        return_ty: ret_ty.clone(),
        trait_env,
        env: &mut env,
        var_gen: &var_gen,
        tys,
        preds: &mut preds,
        exceptions,
        assumps: &assumps,
        local_gen: 0,
    };

    if let Some(body) = &mut fun.node.body.as_mut() {
        check_stmts(&mut tc_state, body, Some(&ret_ty), 0, &mut Vec::new());
    }

    resolve_preds(trait_env, &assumps, tys.tys.cons(), preds, &var_gen, 0);

    if let Some(body) = &mut fun.node.body.as_mut() {
        for stmt in body.iter_mut() {
            normalize_stmt(
                &mut stmt.node,
                &stmt.loc,
                tys.tys.cons(),
                trait_env,
                &var_gen,
            );
        }
    }

    tys.tys.exit_scope();
}

/// Type check a trait implementation.
///
/// `tys` is `mut` to be able to bind type parameters of the `impl` before checking the methods.
fn check_impl(impl_: &mut ast::L<ast::ImplDecl>, tys: &mut PgmTypes, trait_env: &TraitEnv) {
    assert_eq!(tys.tys.len_scopes(), 1);
    tys.tys.enter_scope();

    let impl_assumps =
        convert_and_bind_context(&mut tys.tys, &impl_.node.context, TyVarConversion::ToRVar);

    let trait_ty_con_id = &impl_.node.trait_;

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

    // Add type synonyms for associated type assignments so that e.g. `Item` resolves to the
    // concrete type within impl method bodies.
    for item in &impl_.node.items {
        if let ast::ImplDeclItem::Type { assoc_ty, rhs } = item {
            let converted = convert_ast_ty(&tys.tys, &rhs.node, &rhs.loc);
            tys.tys.insert_synonym(assoc_ty.node.clone(), converted);
        }
    }

    // Check method bodies.
    for item in &mut impl_.node.items {
        let fun = match item {
            ast::ImplDeclItem::Type { .. } => continue,
            ast::ImplDeclItem::Fun(fun) => fun,
        };

        tys.tys.enter_scope();

        // Bind function type parameters.
        let fun_assumps =
            convert_and_bind_context(&mut tys.tys, &fun.node.sig.context, TyVarConversion::ToRVar);

        // Check the body.
        if let Some(body) = &mut fun.node.body {
            let ret_ty = match &fun.node.sig.return_ty {
                Some(ty) => convert_ast_ty(&tys.tys, &ty.node, &ty.loc),
                None => Ty::unit(),
            };

            let mut preds: Vec<Pred> = Default::default();
            let mut env: ScopeMap<Id, Ty> = ScopeMap::default();
            let var_gen = UVarGen::default();

            match &fun.node.sig.self_ {
                ast::SelfParam::No => {}
                ast::SelfParam::Implicit => {
                    // TODO: We can use the `self` type from the trait declaration here.
                    panic!(
                        "{}: `self` parameters without type signatures are not supported yet",
                        loc_display(&fun.loc)
                    );
                }
                ast::SelfParam::Explicit(ty) => {
                    env.insert(
                        SmolStr::new("self"),
                        convert_ast_ty(&tys.tys, &ty.node, &ty.loc),
                    );
                }
            }

            for (param_name, param_ty) in &fun.node.sig.params {
                let param_ty = param_ty.as_ref().unwrap();
                env.insert(
                    param_name.clone(),
                    convert_ast_ty(&tys.tys, &param_ty.node, &param_ty.loc),
                );
            }

            let assumps = impl_assumps
                .iter()
                .cloned()
                .chain(fun_assumps.into_iter())
                .collect();

            let exceptions = match &fun.node.sig.exceptions {
                Some(exc) => convert_ast_ty(&tys.tys, &exc.node, &exc.loc),
                None => panic!(),
            };

            let mut tc_state = TcFunState {
                return_ty: ret_ty.clone(),
                trait_env,
                env: &mut env,
                var_gen: &var_gen,
                tys,
                preds: &mut preds,
                exceptions,
                assumps: &assumps,
                local_gen: 0,
            };

            check_stmts(&mut tc_state, body, Some(&ret_ty), 0, &mut Vec::new());

            resolve_preds(trait_env, &assumps, tys.tys.cons(), preds, &var_gen, 0);

            for stmt in body.iter_mut() {
                normalize_stmt(
                    &mut stmt.node,
                    &stmt.loc,
                    tys.tys.cons(),
                    trait_env,
                    &var_gen,
                );
            }
        }

        tys.tys.exit_scope();
    }

    // Check that all methods without default implementations are implemented.
    let trait_method_ids: HashSet<&Id> = trait_details.methods.keys().collect();
    let mut implemented_method_ids: HashSet<&Id> = Default::default();
    let mut implemented_assoc_tys: HashSet<Id> = Default::default();
    for item in &impl_.node.items {
        let fun = match item {
            ast::ImplDeclItem::Type { assoc_ty, rhs: _ } => {
                if !trait_details.assoc_tys.contains(&assoc_ty.node) {
                    panic!(
                        "{}: Trait {} does not have associated type {}",
                        loc_display(&assoc_ty.loc),
                        &trait_ty_con_id.node,
                        &assoc_ty.node
                    );
                }
                let new = implemented_assoc_tys.insert(assoc_ty.node.clone());
                if !new {
                    panic!(
                        "{}: Associated type {} implemented mutiple times",
                        loc_display(&assoc_ty.loc),
                        assoc_ty.node
                    );
                }
                continue;
            }
            ast::ImplDeclItem::Fun(fun) => fun,
        };
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
                    loc_display(&fun.loc),
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

    let missing_assoc_tys: Vec<&Id> = trait_details
        .assoc_tys
        .difference(&implemented_assoc_tys)
        .collect();
    if !missing_assoc_tys.is_empty() {
        panic!(
            "{}: Associated types missing: {:?}",
            loc_display(&impl_.loc),
            missing_assoc_tys,
        );
    }

    tys.tys.exit_scope();
    assert_eq!(tys.tys.len_scopes(), 1);
}

fn resolve_preds(
    trait_env: &TraitEnv,
    assumps: &[Pred],
    cons: &HashMap<Id, TyCon>,
    mut goals: Vec<Pred>,
    var_gen: &UVarGen,
    _level: u32,
) {
    let mut ambiguous_var_rows: Vec<UVarRef> = vec![];
    let mut ambiguous_rec_rows: Vec<UVarRef> = vec![];

    // TODO: Not sure if this is a bug or not, but resolving a predicate may allow other predicates
    // to be resolved as well. Keep looping as long as we resolve predicates.
    let mut progress = true;

    while progress {
        progress = false;
        let mut next_goals: Vec<Pred> = vec![];

        'goals: while let Some(mut pred) = goals.pop() {
            pred.params
                .iter_mut()
                .for_each(|ty| *ty = ty.deep_normalize(cons, trait_env, var_gen, &[]));

            if pred.trait_ == kind_inference::REC_ROW_TRAIT_ID {
                assert!(pred.assoc_ty.is_none());
                match &pred.params[0] {
                    Ty::Anonymous {
                        record_or_variant,
                        is_row,
                        ..
                    } => {
                        if *is_row && *record_or_variant == RecordOrVariant::Record {
                            continue;
                        }
                    }
                    Ty::UVar(var_ref) => {
                        assert_eq!(var_ref.kind(), Kind::Row(RecordOrVariant::Record));
                        ambiguous_rec_rows.push(var_ref.clone());
                        continue;
                    }
                    _ => {}
                }
            }

            if pred.trait_ == kind_inference::VAR_ROW_TRAIT_ID {
                assert!(pred.assoc_ty.is_none());
                match &pred.params[0] {
                    Ty::Anonymous {
                        record_or_variant,
                        is_row,
                        ..
                    } => {
                        if *is_row && *record_or_variant == RecordOrVariant::Variant {
                            continue;
                        }
                    }
                    Ty::UVar(var_ref) => {
                        assert_eq!(var_ref.kind(), Kind::Row(RecordOrVariant::Variant));
                        ambiguous_var_rows.push(var_ref.clone());
                        continue;
                    }
                    _ => {}
                }
            }

            for assump in assumps {
                // We can't use set lookup as locs will be different.
                if assump.trait_ == pred.trait_ && assump.params == pred.params {
                    match (&assump.assoc_ty, &pred.assoc_ty) {
                        (None, None) => {
                            // No need to flip `progress` as we haven't done any unification.
                            continue 'goals;
                        }
                        (Some((assump_name, assump_rhs)), Some((pred_name, pred_rhs)))
                            if assump_name == pred_name =>
                        {
                            unification::unify(
                                assump_rhs,
                                pred_rhs,
                                cons,
                                trait_env,
                                var_gen,
                                0,
                                &pred.loc,
                                &[],
                                &mut next_goals,
                            );
                            progress = true;
                            continue 'goals;
                        }
                        _ => {}
                    }
                }
            }

            let trait_impls = match trait_env.get(&pred.trait_) {
                Some(impls) => impls,
                None => panic!(
                    "{}: Unable to resolve pred {}",
                    loc_display(&pred.loc.clone()),
                    Pred {
                        trait_: pred.trait_,
                        params: pred.params,
                        assoc_ty: pred.assoc_ty,
                        loc: pred.loc
                    },
                ),
            };

            for impl_ in trait_impls {
                if let Some((subgoals, assoc_tys)) =
                    impl_.try_match(&pred.params, var_gen, cons, &pred.loc)
                {
                    if let Some((goal_assoc_ty, goal_assoc_ty_rhs)) = &pred.assoc_ty {
                        let matching_assoc_ty_rhs = assoc_tys.get(goal_assoc_ty).unwrap();
                        // Associated types don't influence implementation search, if we found an
                        // implementation its associated types should unify with the expected types
                        // or the search fails.
                        // Full unification is needed here because both sides may contain `UVar`s:
                        // the goal RHS from inference, and the matching RHS from `try_match`
                        // creating fresh `UVar`s for the impl's quantified variables.
                        unification::unify(
                            goal_assoc_ty_rhs,
                            matching_assoc_ty_rhs,
                            cons,
                            trait_env,
                            var_gen,
                            0,
                            &pred.loc,
                            &[],
                            &mut next_goals,
                        );
                    }
                    next_goals.extend(subgoals);
                    progress = true;
                    continue 'goals;
                }
            }

            // Try again after making progress (unifying stuff).
            next_goals.push(pred);
        }

        goals = next_goals;
    }

    if !goals.is_empty() {
        goals.sort();
        use std::fmt::Write;
        let mut msg = String::new();
        writeln!(&mut msg, "Unable to resolve predicates:").unwrap();
        for goal in goals {
            writeln!(&mut msg, "{}: {}", loc_display(&goal.loc.clone()), goal).unwrap();
        }
        panic!("{}", msg);
    }

    for rec_row in ambiguous_rec_rows {
        if rec_row.link().is_none() {
            rec_row.set_link(Ty::Anonymous {
                labels: Default::default(),
                extension: None,
                record_or_variant: RecordOrVariant::Record,
                is_row: true,
            });
        }
    }

    for var_row in ambiguous_var_rows {
        if var_row.link().is_none() {
            var_row.set_link(Ty::Anonymous {
                labels: Default::default(),
                extension: None,
                record_or_variant: RecordOrVariant::Variant,
                is_row: true,
            });
        }
    }
}

fn rename_domain_var(var: &Id, uniq: u32) -> Id {
    // Add the comment character '#' to make sure it won't conflict with a user variable.
    SmolStr::new(format!("{var}#{uniq}"))
}

/// Expand type synonym references some of the `ast::Type` nodes in the module. This must run after
/// type checking and before monomorphization.
///
/// This only expands type synonyms in the `ast::Type`s in the AST that the monomorphiser uses. E.g.
/// it doesn't expand synonyms in `let` binding type annotations because monomorphiser doesn't use
/// those.
pub(crate) fn expand_type_synonyms(module: &mut ast::Module) {
    // Collect top-level synonyms.
    let mut synonyms: HashMap<Id, ast::Type> = Default::default();
    for decl in module.iter() {
        if let ast::TopDecl::Type(ty_decl) = &decl.node
            && let Some(ast::TypeDeclRhs::Synonym(rhs)) = &ty_decl.node.rhs
        {
            synonyms.insert(ty_decl.node.name.clone(), rhs.node.clone());
        }
    }

    for decl in module.iter_mut() {
        match &mut decl.node {
            ast::TopDecl::Type(ty_decl) => {
                expand_synonyms_in_type_decl(&mut ty_decl.node, &synonyms);
            }

            ast::TopDecl::Fun(fun) => {
                expand_synonyms_in_fun(&mut fun.node, &synonyms);
            }

            ast::TopDecl::Trait(trait_decl) => {
                // Build scoped synonyms: trait associated types map to AssocTySelect.
                let mut scoped = synonyms.clone();
                for item in &trait_decl.node.items {
                    if let ast::TraitDeclItem::Type(assoc_ty) = item {
                        let trait_ty = ast::Type::Named(ast::NamedType {
                            name: trait_decl.node.name.node.clone(),
                            args: trait_decl
                                .node
                                .type_params
                                .iter()
                                .map(|p| p.map_as_ref(|p| ast::Type::Var(p.clone())))
                                .collect(),
                        });
                        scoped.insert(
                            assoc_ty.node.clone(),
                            ast::Type::AssocTySelect {
                                ty: assoc_ty.set_node(Box::new(trait_ty)),
                                assoc_ty: assoc_ty.node.clone(),
                            },
                        );
                    }
                }

                for item in &mut trait_decl.node.items {
                    if let ast::TraitDeclItem::Fun(fun) = item {
                        expand_synonyms_in_fun(&mut fun.node, &scoped);
                    }
                }
            }

            ast::TopDecl::Impl(impl_decl) => {
                // Build scoped synonyms: impl associated type assignments.
                let mut scoped = synonyms.clone();
                for item in &impl_decl.node.items {
                    if let ast::ImplDeclItem::Type { assoc_ty, rhs } = item {
                        // First expand any synonyms in the RHS itself.
                        let mut rhs_expanded = rhs.node.clone();
                        expand_synonyms_in_ty(&mut rhs_expanded, &synonyms);
                        scoped.insert(assoc_ty.node.clone(), rhs_expanded);
                    }
                }

                for item in &mut impl_decl.node.items {
                    match item {
                        ast::ImplDeclItem::Type { assoc_ty: _, rhs } => {
                            expand_synonyms_in_ty(&mut rhs.node, &synonyms);
                        }
                        ast::ImplDeclItem::Fun(fun) => {
                            expand_synonyms_in_fun(&mut fun.node, &scoped);
                        }
                    }
                }
            }

            ast::TopDecl::Import(_) => {}
        }
    }
}

fn expand_synonyms_in_type_decl(decl: &mut ast::TypeDecl, synonyms: &HashMap<Id, ast::Type>) {
    match &mut decl.rhs {
        Some(ast::TypeDeclRhs::Sum { cons, extension }) => {
            for con in cons {
                expand_synonyms_in_fields(&mut con.fields, synonyms);
            }
            if let Some(ext) = extension {
                expand_synonyms_in_ty(&mut ext.node, synonyms);
            }
        }
        Some(ast::TypeDeclRhs::Product(fields)) => {
            expand_synonyms_in_fields(fields, synonyms);
        }
        Some(ast::TypeDeclRhs::Synonym(rhs)) => {
            expand_synonyms_in_ty(&mut rhs.node, synonyms);
        }
        None => {}
    }
}

fn expand_synonyms_in_fields(fields: &mut ast::ConFields, synonyms: &HashMap<Id, ast::Type>) {
    match fields {
        ast::ConFields::Empty => {}
        ast::ConFields::Named { fields, extension } => {
            for (_, ty) in fields {
                expand_synonyms_in_ty(&mut ty.node, synonyms);
            }
            if let Some(ext) = extension {
                expand_synonyms_in_ty(&mut ext.node, synonyms);
            }
        }
        ast::ConFields::Unnamed { fields } => {
            for ty in fields {
                expand_synonyms_in_ty(&mut ty.node, synonyms);
            }
        }
    }
}

fn expand_synonyms_in_fun(fun: &mut ast::FunDecl, synonyms: &HashMap<Id, ast::Type>) {
    expand_synonyms_in_sig(&mut fun.sig, synonyms);
}

fn expand_synonyms_in_sig(sig: &mut ast::FunSig, synonyms: &HashMap<Id, ast::Type>) {
    if let ast::SelfParam::Explicit(ty) = &mut sig.self_ {
        expand_synonyms_in_ty(&mut ty.node, synonyms);
    }
    for (_, ty) in &mut sig.params {
        if let Some(ty) = ty {
            expand_synonyms_in_ty(&mut ty.node, synonyms);
        }
    }
    if let Some(ty) = &mut sig.return_ty {
        expand_synonyms_in_ty(&mut ty.node, synonyms);
    }
    if let Some(ty) = &mut sig.exceptions {
        expand_synonyms_in_ty(&mut ty.node, synonyms);
    }
}

fn expand_synonyms_in_ty(ty: &mut ast::Type, synonyms: &HashMap<Id, ast::Type>) {
    match ty {
        ast::Type::Named(named) => {
            if let Some(expansion) = synonyms.get(&named.name) {
                assert!(named.args.is_empty());
                *ty = expansion.clone();
                // Recursively expand in case the expansion contains more synonyms.
                expand_synonyms_in_ty(ty, synonyms);
                return;
            }
            for arg in &mut named.args {
                expand_synonyms_in_ty(&mut arg.node, synonyms);
            }
        }

        ast::Type::Var(_) => {}

        ast::Type::Record {
            fields,
            extension,
            is_row: _,
        } => {
            for (_, field_ty) in fields {
                expand_synonyms_in_ty(field_ty, synonyms);
            }
            if let Some(ext) = extension {
                expand_synonyms_in_ty(&mut ext.node, synonyms);
            }
        }

        ast::Type::Variant {
            alts,
            extension,
            is_row: _,
        } => {
            for alt in alts {
                for arg in &mut alt.args {
                    expand_synonyms_in_ty(&mut arg.node, synonyms);
                }
            }
            if let Some(ext) = extension {
                expand_synonyms_in_ty(&mut ext.node, synonyms);
            }
        }

        ast::Type::Fn(fn_ty) => {
            for arg in &mut fn_ty.args {
                expand_synonyms_in_ty(&mut arg.node, synonyms);
            }
            if let Some(ret) = &mut fn_ty.ret {
                expand_synonyms_in_ty(&mut ret.node, synonyms);
            }
            if let Some(exn) = &mut fn_ty.exceptions {
                expand_synonyms_in_ty(&mut exn.node, synonyms);
            }
        }

        ast::Type::AssocTySelect {
            ty: inner,
            assoc_ty: _,
        } => {
            expand_synonyms_in_ty(&mut inner.node, synonyms);
        }
    }
}
