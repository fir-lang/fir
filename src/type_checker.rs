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
mod traits;
mod ty;
mod ty_map;
mod unification;

pub use crate::utils::loc_display;
use convert::convert_fields;
use convert::*;
use instantiation::normalize_instantiation_types;
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
    pub top_schemes: Map<Id, Scheme>,

    /// Type schemes of associated functions.
    ///
    /// These include methods (associated functions with a `self` parameter).
    pub associated_fn_schemes: Map<Id, Map<Id, Scheme>>,

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
    pub method_schemes: Map<Id, Vec<(Id, Scheme)>>,

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
                        fun.sig.exceptions = Some(exn_type(
                            fun.name.loc.module.clone(),
                            fun.name.loc.line_start,
                        ));
                    }
                }
            }

            ast::TopDecl::Trait(ast::L { node, .. }) => {
                for fun in &mut node.items {
                    if fun.node.sig.exceptions.is_none() {
                        fun.node.sig.exceptions =
                            Some(exn_type(fun.loc.module.clone(), fun.loc.line_start));
                    }
                }
            }

            ast::TopDecl::Impl(ast::L { node, .. }) => {
                for fun in &mut node.items {
                    if fun.node.sig.exceptions.is_none() {
                        fun.node.sig.exceptions =
                            Some(exn_type(fun.loc.module.clone(), fun.loc.line_start));
                    }
                }
            }

            ast::TopDecl::Import(_) | ast::TopDecl::Type(_) => {}
        }
    }
}

// The default exception type: `[..?exn]`.
fn exn_type(module: std::rc::Rc<str>, line: u16) -> ast::L<ast::Type> {
    ast::L {
        node: ast::Type::Variant {
            alts: Default::default(),
            extension: Some(EXN_QVAR_ID),
        },
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

                let _trait_context: Set<Pred> = convert_and_bind_context(
                    &mut tys,
                    &trait_context_ast,
                    TyVarConversion::ToQVar,
                    &trait_decl.loc,
                );

                let mut methods: Map<Id, TraitMethod> =
                    Map::with_capacity_and_hasher(trait_decl.node.items.len(), Default::default());

                for fun in &trait_decl.node.items {
                    // New scope for function context.
                    tys.enter_scope();

                    let fun_preds: Set<Pred> = convert_and_bind_context(
                        &mut tys,
                        &fun.node.sig.context,
                        TyVarConversion::ToQVar,
                        &fun.loc,
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

                    methods.insert(fun.node.name.node.clone(), {
                        TraitMethod {
                            scheme,
                            fun_decl: fun.clone(),
                        }
                    });
                }

                let ty_con = tys.get_con_mut(&trait_decl.node.name.node).unwrap();
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

        let _impl_context = convert_and_bind_context(
            &mut tys,
            &impl_decl.context,
            TyVarConversion::ToQVar,
            &decl.loc,
        );

        let trait_ty_con = tys.get_con_mut(trait_con_id).unwrap(); // checked above
        let trait_type_params = &trait_ty_con.ty_params;
        let trait_methods = match &mut trait_ty_con.details {
            TyConDetails::Trait(TraitDetails { ref methods }) => methods,
            TyConDetails::Type { .. } | TyConDetails::Synonym(_) => {
                panic!() // checked above
            }
        };

        for (method, method_decl) in trait_methods {
            if method_decl.fun_decl.node.body.is_none() {
                continue;
            }

            if impl_decl
                .items
                .iter()
                .any(|item| &item.node.name.node == method)
            {
                continue;
            }

            let mut fun_decl = method_decl.fun_decl.clone();

            // Map type parameters of the trait to the impl types.
            let substs: Map<Id, ast::Type> = trait_type_params
                .iter()
                .map(|(param, _param_kind)| param.clone())
                .zip(impl_decl.tys.iter().map(|ty| ty.node.clone()))
                .collect();

            fun_decl.node.sig.self_ = match fun_decl.node.sig.self_ {
                ast::SelfParam::No => ast::SelfParam::No,
                ast::SelfParam::Implicit => ast::SelfParam::Implicit,
                ast::SelfParam::Explicit(ty) => {
                    ast::SelfParam::Explicit(ty.map_as_ref(|ty| ty.subst_ids(&substs)))
                }
            };

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

            fun_decl.loc = decl.loc.clone();

            impl_decl.items.push(fun_decl);
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
    Map<Id, Vec<(Id, Scheme)>>,
) {
    let mut top_schemes: Map<Id, Scheme> = Default::default();
    let mut associated_fn_schemes: Map<Id, Map<Id, Scheme>> = Default::default();
    let mut method_schemes: Map<Id, Vec<(Id, Scheme)>> = Default::default();

    for decl in module {
        // New scope for type and function contexts.
        assert_eq!(tys.len_scopes(), 1);
        tys.enter_scope();

        match &decl.node {
            ast::TopDecl::Trait(trait_decl) => {
                /*
                trait ToStr[t]:
                    toStr(self: t): Str
                ==>
                toStr[ToStr[t]](self: t): Str

                trait Iterator[iter, item]:
                    next(self: Iterator[iter, item]): Option[item]
                ==>
                next[Iterator[iter, item]](self: Iterator[iter, item]): Option[item]
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

                let trait_pred = ast::L {
                    loc: trait_decl.loc.clone(),
                    node: ast::Type::Named(ast::NamedType {
                        name: trait_decl.node.name.node.clone(),
                        args: trait_decl
                            .node
                            .type_params
                            .iter()
                            .map(|param| param.map_as_ref(|param| ast::Type::Var(param.clone())))
                            .collect(),
                    }),
                };

                for fun in &trait_decl.node.items {
                    // Add trait type parameters and predicate to the function context before
                    // converting.
                    // Note: This needs to be a `Vec` instead of `Map`. See the comments around
                    // `trait_quantified_vars`.
                    let mut fun_type_params = trait_quantified_vars.clone();
                    fun_type_params.extend(fun.node.sig.context.type_params.clone());

                    let mut fun_preds = vec![trait_pred.clone()];
                    fun_preds.extend(fun.node.sig.context.preds.clone());

                    let context = ast::Context {
                        type_params: fun_type_params,
                        preds: fun_preds,
                    };

                    // TODO: Checking is the same as top-level functions, maybe move the code into a
                    // function and reuse.
                    let fun_preds: Set<Pred> =
                        convert_and_bind_context(tys, &context, TyVarConversion::ToQVar, &fun.loc);

                    let mut arg_tys: Vec<Ty> = fun
                        .node
                        .sig
                        .params
                        .iter()
                        .map(|(_name, ty)| convert_ast_ty(tys, &ty.node, &ty.loc))
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
                        args: FunArgs::Positional(arg_tys),
                        ret: Box::new(ret_ty),
                        exceptions: Some(Box::new(exceptions)),
                    };

                    let scheme = Scheme {
                        quantified_vars: context.type_params.into_iter().collect(),
                        preds: fun_preds,
                        ty: fun_ty,
                        loc: fun.loc.clone(),
                    };

                    method_schemes
                        .entry(fun.node.name.node.clone())
                        .or_default()
                        .push((trait_decl.node.name.node.clone(), scheme));
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
                let fun_preds: Set<Pred> =
                    convert_and_bind_context(tys, &sig.context, TyVarConversion::ToQVar, loc);

                let mut arg_tys: Vec<Ty> = sig
                    .params
                    .iter()
                    .map(|(_name, ty)| convert_ast_ty(tys, &ty.node, &ty.loc))
                    .collect();

                match &sig.self_ {
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
                        ty_decl
                            .node
                            .type_params
                            .iter()
                            .map(|ty_var| Ty::QVar(ty_var.clone()))
                            .collect(),
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

            ast::TopDecl::Impl(impl_decl) => {
                // Default methods are already copied to impls. Check that impl method signatures
                // match the trait method signatures.
                let impl_assumps = convert_and_bind_context(
                    tys,
                    &impl_decl.node.context,
                    TyVarConversion::ToQVar,
                    &impl_decl.loc,
                );

                for fun in &impl_decl.node.items {
                    let sig = &fun.node.sig;

                    let fun_assumps = convert_and_bind_context(
                        tys,
                        &sig.context,
                        TyVarConversion::ToQVar,
                        &fun.loc,
                    );

                    let mut arg_tys: Vec<Ty> = sig
                        .params
                        .iter()
                        .map(|(_name, ty)| convert_ast_ty(tys, &ty.node, &ty.loc))
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
                        args: FunArgs::Positional(arg_tys),
                        ret: Box::new(ret_ty),
                        exceptions: Some(Box::new(exceptions)),
                    };

                    let impl_fun_scheme = Scheme {
                        quantified_vars: impl_decl
                            .node
                            .context
                            .type_params
                            .iter()
                            .cloned()
                            .chain(fun.node.sig.context.type_params.iter().cloned())
                            .collect(),
                        preds: impl_assumps
                            .iter()
                            .cloned()
                            .chain(fun_assumps.iter().cloned())
                            .collect(),
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

                    let mut trait_fun_scheme = trait_fun_scheme0.clone();

                    // Substitute trait arguments. Add free variables of the arguments to the
                    // context.

                    /*
                    // TODO: FIXME: Variables already bound in the trait type scheme should be renamed.
                    let bound_vars: Set<&Id> = trait_fun_scheme
                        .quantified_vars
                        .iter()
                        .map(|(id, _)| id)
                        .collect();
                    */

                    let mut arg_fvs: OrderMap<Id, Option<Kind>> = Default::default();

                    for ((ty_param, _), ty_arg) in
                        trait_ty_con.ty_params.iter().zip(impl_decl.node.tys.iter())
                    {
                        kind_inference::collect_tvs(&ty_arg.node, &ty_arg.loc, &mut arg_fvs);
                        let ty_arg = convert_ast_ty(tys, &ty_arg.node, &ty_arg.loc);
                        trait_fun_scheme = trait_fun_scheme.subst(ty_param, &ty_arg);
                    }

                    trait_fun_scheme.quantified_vars.splice(
                        0..0,
                        arg_fvs
                            .into_iter()
                            .map(|(id, kind)| (id, kind.unwrap_or(Kind::Star))),
                    );

                    if !trait_fun_scheme.eq_modulo_alpha(
                        tys.cons(),
                        &Default::default(),
                        &impl_fun_scheme,
                        &fun.loc,
                    ) {
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
    let mut var_gen = TyVarGen::default();
    let mut env: ScopeMap<Id, Ty> = ScopeMap::default();

    assert_eq!(tys.tys.len_scopes(), 1);
    tys.tys.enter_scope();

    // The predicates that we assume to hold in the function body.
    let assumps = convert_and_bind_context(
        &mut tys.tys,
        &fun.node.sig.context,
        TyVarConversion::ToOpaque,
        &fun.loc,
    );

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
                        Ty::Con(parent_ty_con.id.clone()),
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

    let exceptions = match &fun.node.sig.exceptions {
        Some(exc) => convert_ast_ty(&tys.tys, &exc.node, &exc.loc),
        None => panic!(),
    };

    let mut tc_state = TcFunState {
        return_ty: ret_ty.clone(),
        trait_env,
        env: &mut env,
        var_gen: &mut var_gen,
        tys,
        preds: &mut preds,
        exceptions,
    };

    if let Some(body) = &mut fun.node.body.as_mut() {
        check_stmts(&mut tc_state, body, Some(&ret_ty), 0, &mut Vec::new());
    }

    resolve_preds(trait_env, &assumps, tys, preds, &mut var_gen, 0);

    if let Some(body) = &mut fun.node.body.as_mut() {
        for stmt in body.iter_mut() {
            normalize_instantiation_types(&mut stmt.node, tys.tys.cons());
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

    let impl_assumps = convert_and_bind_context(
        &mut tys.tys,
        &impl_.node.context,
        TyVarConversion::ToOpaque,
        &impl_.loc,
    );

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

    // Check method bodies.
    for fun in &mut impl_.node.items {
        tys.tys.enter_scope();

        // Bind function type parameters.
        let fun_assumps = convert_and_bind_context(
            &mut tys.tys,
            &fun.node.sig.context,
            TyVarConversion::ToOpaque,
            &fun.loc,
        );

        // Check the body.
        if let Some(body) = &mut fun.node.body {
            let ret_ty = match &fun.node.sig.return_ty {
                Some(ty) => convert_ast_ty(&tys.tys, &ty.node, &ty.loc),
                None => Ty::unit(),
            };

            let mut preds: Set<Pred> = Default::default();
            let mut env: ScopeMap<Id, Ty> = ScopeMap::default();
            let mut var_gen = TyVarGen::default();

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
                var_gen: &mut var_gen,
                tys,
                preds: &mut preds,
                exceptions,
            };

            check_stmts(&mut tc_state, body, Some(&ret_ty), 0, &mut Vec::new());

            resolve_preds(trait_env, &assumps, tys, preds, &mut var_gen, 0);

            for stmt in body.iter_mut() {
                normalize_instantiation_types(&mut stmt.node, tys.tys.cons());
            }
        }

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

    tys.tys.exit_scope();
    assert_eq!(tys.tys.len_scopes(), 1);
}

fn resolve_preds(
    trait_env: &TraitEnv,
    assumps: &Set<Pred>,
    tys: &PgmTypes,
    preds: Set<Pred>,
    var_gen: &mut TyVarGen,
    _level: u32,
) {
    let mut goals: Vec<Pred> = preds.into_iter().collect();
    let mut ambiguous_var_rows: Vec<TyVarRef> = vec![];
    let mut ambiguous_rec_rows: Vec<TyVarRef> = vec![];

    'goals: while let Some(mut pred) = goals.pop() {
        // Normalize to improve error messages.
        pred.params
            .iter_mut()
            .for_each(|ty| *ty = ty.normalize(tys.tys.cons()));

        if pred.trait_ == "RecRow" {
            match &pred.params[0] {
                Ty::Anonymous { kind, is_row, .. } => {
                    if *is_row && *kind == RecordOrVariant::Record {
                        continue;
                    }
                }
                Ty::Var(var_ref) => {
                    assert_eq!(var_ref.kind(), Kind::Row(RecordOrVariant::Record));
                    ambiguous_rec_rows.push(var_ref.clone());
                    continue;
                }
                _ => {}
            }
        }

        if pred.trait_ == "VarRow" {
            match &pred.params[0] {
                Ty::Anonymous { kind, is_row, .. } => {
                    if *is_row && *kind == RecordOrVariant::Variant {
                        continue;
                    }
                }
                Ty::Var(var_ref) => {
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
                continue 'goals;
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
                    loc: pred.loc
                },
            ),
        };

        for impl_ in trait_impls {
            if let Some(subgoals) = impl_.try_match(&pred.params, var_gen, &tys.tys, &pred.loc) {
                goals.extend(subgoals.into_iter().map(|(trait_, params)| Pred {
                    trait_,
                    params,
                    loc: pred.loc.clone(),
                }));
                continue 'goals;
            }
        }

        panic!(
            "{}: Unable to resolve {}",
            loc_display(&pred.loc.clone()),
            Pred {
                trait_: pred.trait_,
                params: pred.params,
                loc: pred.loc
            },
        );
    }

    for rec_row in ambiguous_rec_rows {
        if rec_row.link().is_none() {
            rec_row.set_link(Ty::Anonymous {
                labels: Default::default(),
                extension: None,
                kind: RecordOrVariant::Record,
                is_row: true,
            });
        }
    }

    for var_row in ambiguous_var_rows {
        if var_row.link().is_none() {
            var_row.set_link(Ty::Anonymous {
                labels: Default::default(),
                extension: None,
                kind: RecordOrVariant::Variant,
                is_row: true,
            });
        }
    }
}
