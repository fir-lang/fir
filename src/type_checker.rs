#![allow(clippy::mutable_key_type, clippy::for_kv_map)]

mod apply;
mod convert;
mod expr;
mod instantiation;
mod pat;
mod row_utils;
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
pub use ty::{Ty, TyArgs};
use ty_map::TyMap;

use crate::ast::{self, Id};
use crate::collections::{Map, ScopeMap, Set};

use smol_str::SmolStr;

/// Type constructors and types in the program.
#[derive(Debug)]
pub struct PgmTypes {
    /// Type schemes of top-level values.
    pub top_schemes: Map<Id, Scheme>,

    /// Type schemes of associated functions and constructors.
    pub associated_fn_schemes: Map<Id, Map<Id, Scheme>>,

    /// Type schemes of methods.
    ///
    /// Methods take a receiver.
    pub method_schemes: Map<Id, Map<Id, Scheme>>,

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

struct TcFunState<'a> {
    context: &'a Map<Id, Map<Id, Map<Id, Ty>>>,
    return_ty: &'a Ty,
    env: &'a mut ScopeMap<Id, Ty>,
    var_gen: &'a mut TyVarGen,
    tys: &'a PgmTypes,
    preds: &'a mut PredSet,
}

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

    // Collect all type constructors first, then add bounds, fields, and methods.
    for decl in module.iter() {
        match &decl.node {
            ast::TopDecl::Type(ty_decl) => {
                let ty_name = ty_decl.node.name.clone();
                let ty_params = ty_decl.node.type_params.clone();
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
                        ty_params: ty_params
                            .into_iter()
                            .map(|ty| (ty, Default::default()))
                            .collect(),
                        assoc_tys: Default::default(),
                        details: TyConDetails::Type(TypeDetails { cons: vec![] }),
                    },
                );
            }

            ast::TopDecl::Trait(trait_decl) => {
                let ty_name = trait_decl.node.name.node.clone();
                let ty_params = vec![trait_decl.node.ty.node.0.clone()];
                if tys.has_con(&ty_name) {
                    panic!(
                        "{}: Type {} is defined multiple times",
                        loc_display(&decl.loc),
                        ty_name
                    );
                }

                let mut assoc_tys: Set<Id> = Default::default();
                for item in &trait_decl.node.items {
                    if let ast::TraitDeclItem::AssocTy(assoc_ty_id) = &item.node {
                        let new = assoc_tys.insert(assoc_ty_id.clone());
                        if !new {
                            panic!(
                                "{}: Associated type {} is defined multiple times",
                                loc_display(&item.loc),
                                assoc_ty_id
                            );
                        }
                    }
                }

                tys.insert_con(
                    ty_name.clone(),
                    TyCon {
                        id: ty_name.clone(),
                        ty_params: ty_params
                            .into_iter()
                            .map(|ty| (ty, Default::default()))
                            .collect(),
                        assoc_tys: Default::default(),
                        details: TyConDetails::Trait(TraitDetails {
                            methods: Default::default(),
                            assoc_tys,
                            implementing_tys: Default::default(),
                        }),
                    },
                );
            }

            ast::TopDecl::Import(_) | ast::TopDecl::Fun(_) | ast::TopDecl::Impl(_) => continue,
        }
    }

    // Add bounds, fields, methods.
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

                // Context syntax in trait declarations is simpler as we allow only one type
                // parameter. Convert the syntax to the more general syntax accepted by the
                // conversion function.
                let trait_context_ast: ast::Context = vec![ast::L {
                    node: (
                        ast::L {
                            node: trait_decl.node.ty.node.0.clone(),
                            loc: trait_decl.node.ty.loc.clone(),
                        },
                        trait_decl.node.ty.node.1.clone(),
                    ),
                    loc: trait_decl.node.ty.loc.clone(),
                }];

                let trait_context = convert_and_bind_context(
                    &mut tys,
                    &trait_context_ast,
                    TyVarConversion::ToQVar,
                    &trait_decl.loc,
                );

                // Convert bounds before binding associated types and self.
                let bounds: Map<Id, Map<Id, Ty>> = trait_decl
                    .node
                    .ty
                    .node
                    .1
                    .iter()
                    .map(|bound| convert_bound(&tys, bound))
                    .collect();

                // E.g. `T` in `trait Debug[T]: ...`.
                let self_ty_id: Id = trait_decl.node.ty.node.0.clone();

                // The `QVar` for `T` in the example. `T` will be mapped to this when converting
                // types.
                let self_ty = Ty::QVar(self_ty_id.clone());

                // Bind assocaited types.
                let assoc_tys: Set<Id> = trait_decl
                    .node
                    .items
                    .iter()
                    .filter_map(|item| match &item.node {
                        ast::TraitDeclItem::AssocTy(ty) => Some(ty.clone()),
                        ast::TraitDeclItem::Fun(_) => None,
                    })
                    .collect();

                for assoc_ty in &assoc_tys {
                    tys.insert_con(assoc_ty.clone(), TyCon::opaque(assoc_ty.clone()));
                    tys.insert_var(
                        assoc_ty.clone(),
                        Ty::AssocTySelect {
                            ty: Box::new(Ty::Con("Self".into())),
                            assoc_ty: assoc_ty.clone(),
                        },
                    );
                }

                // Bind `Self`.
                tys.insert_con(
                    "Self".into(),
                    TyCon {
                        id: "Self".into(),
                        ty_params: vec![],
                        assoc_tys: Default::default(),
                        details: TyConDetails::Synonym(self_ty.clone()),
                    },
                );
                tys.insert_var("Self".into(), Ty::Con("Self".into()));

                let methods: Map<Id, TraitMethod> = trait_decl
                    .node
                    .items
                    .iter()
                    .filter_map(|item| match &item.node {
                        ast::TraitDeclItem::AssocTy(_) => None,
                        ast::TraitDeclItem::Fun(fun) => {
                            // New scope for function context.
                            tys.enter_scope();

                            let fun_context = convert_and_bind_context(
                                &mut tys,
                                &fun.sig.type_params,
                                TyVarConversion::ToQVar,
                                &item.loc,
                            );

                            if fun.sig.self_ {
                                tys.insert_var(SmolStr::new_static("self"), self_ty.clone());
                            }

                            let mut arg_tys: Vec<Ty> = fun
                                .sig
                                .params
                                .iter()
                                .map(|(_name, ty)| convert_ast_ty(&tys, &ty.node, &ty.loc))
                                .collect();

                            if fun.sig.self_ {
                                arg_tys.insert(0, self_ty.clone());
                            }

                            let ret_ty: Ty = match &fun.sig.return_ty {
                                Some(ret_ty) => convert_ast_ty(&tys, &ret_ty.node, &ret_ty.loc),
                                None => Ty::unit(),
                            };

                            let fun_ty = Ty::Fun(arg_tys, Box::new(ret_ty));

                            tys.exit_scope();

                            let scheme = Scheme {
                                quantified_vars: trait_context
                                    .iter()
                                    .cloned()
                                    .chain(fun_context.into_iter())
                                    .collect(),
                                ty: fun_ty,
                                loc: item.loc.clone(),
                            };

                            Some((fun.sig.name.node.clone(), {
                                let fun_decl = fun.clone();
                                TraitMethod {
                                    scheme,
                                    fun_decl: item.set_node(fun_decl),
                                }
                            }))
                        }
                    })
                    .collect();

                let ty_con = tys.get_con_mut(&trait_decl.node.name.node).unwrap();
                assert_eq!(ty_con.ty_params.len(), 1);

                ty_con.ty_params[0].1 = bounds;
                ty_con.details = TyConDetails::Trait(TraitDetails {
                    methods,
                    assoc_tys,
                    implementing_tys: Default::default(),
                });

                tys.exit_scope();
                assert_eq!(tys.len_scopes(), 1);
            }

            ast::TopDecl::Fun(_) | ast::TopDecl::Import(_) | ast::TopDecl::Impl(_) => continue,
        }
    }

    // Add default methods to impls, and populate the trait->implementing types map, check
    // associated types, add associated types to `TyCon`s.
    //
    // We don't need to type check default methods copied to impls, but for now we do. So replace
    // the trait type parameter with the self type in the copied declarations.
    for decl in module.iter_mut() {
        let impl_decl = match &mut decl.node {
            ast::TopDecl::Impl(impl_decl) => &mut impl_decl.node,
            _ => continue,
        };

        let trait_con_id = match &impl_decl.trait_ {
            Some(trait_id) => &trait_id.node,
            None => continue,
        };

        // New scope for the context.
        assert_eq!(tys.len_scopes(), 1);
        tys.enter_scope();

        let _impl_context = convert_and_bind_context(
            &mut tys,
            &impl_decl.context,
            TyVarConversion::ToQVar,
            &decl.loc,
        );

        let impl_ty = convert_ast_ty(&tys, &impl_decl.ty.node, &impl_decl.ty.loc);

        let trait_ty_con = tys.get_con_mut(trait_con_id).unwrap_or_else(|| {
            panic!("{}: Unknown trait {}", loc_display(&decl.loc), trait_con_id)
        });

        let (trait_methods, trait_assoc_tys, trait_implementing_tys) =
            match &mut trait_ty_con.details {
                TyConDetails::Trait(TraitDetails {
                    ref methods,
                    ref assoc_tys,
                    ref mut implementing_tys,
                }) => (methods, assoc_tys, implementing_tys),

                TyConDetails::Type { .. } | TyConDetails::Synonym(_) => {
                    panic!(
                        "{}: {} in impl declararation is not a trait",
                        loc_display(&decl.loc),
                        trait_con_id
                    );
                }
            };

        // Check that associated types are defined only once.
        let mut defined_assoc_tys: Set<Id> = Default::default();
        for item in &impl_decl.items {
            if let ast::ImplDeclItem::AssocTy(impl_assoc_ty) = &item.node {
                let new = defined_assoc_tys.insert(impl_assoc_ty.name.clone());
                if !new {
                    panic!(
                        "{}: Associated type {} is defined multiple times",
                        loc_display(&item.loc),
                        impl_assoc_ty.name
                    );
                }
            }
        }

        // Check that all associated types of the trait are implemented, and no extra associated
        // types are defined.
        if &defined_assoc_tys != trait_assoc_tys {
            let extras: Set<&Id> = defined_assoc_tys.difference(trait_assoc_tys).collect();
            if !extras.is_empty() {
                panic!(
                    "{}: Extra associated types defined: {:?}",
                    loc_display(&decl.loc),
                    extras
                );
            }

            let missing: Set<&Id> = trait_assoc_tys.difference(&defined_assoc_tys).collect();
            if !missing.is_empty() {
                panic!(
                    "{}: Missing associated types: {:?}",
                    loc_display(&decl.loc),
                    missing
                );
            }
        }

        // Type parameter of the trait, e.g. `T` in `trait Debug[T]: ...`.
        let trait_ty_param: Id = trait_ty_con.ty_params[0].0.clone();

        // Type constructor of the type implementing the trait.
        // TODO: We are passing empty con map here to avoid borrow checking issues. This will fail
        // when the trait arugment is a type synonym, which we should reject anyway, but with a
        // proper error message.
        let (self_ty_con, _) = impl_ty.con(&Default::default()).unwrap();

        if !trait_implementing_tys.insert(self_ty_con.clone()) {
            panic!(
                "{}: Trait {} is implemented for type {} multiple times",
                loc_display(&decl.loc),
                trait_con_id,
                self_ty_con
            );
        }

        for (method, method_decl) in trait_methods {
            if impl_decl.items.iter().any(|item| match &item.node {
                ast::ImplDeclItem::AssocTy(_) => false,
                ast::ImplDeclItem::Fun(fun) => &fun.sig.name.node == method,
            }) {
                continue;
            }

            if method_decl.fun_decl.node.body.is_some() {
                let mut fun_decl = method_decl.fun_decl.clone();
                // TODO: For now we only replace trait type param with self in the signature, but
                // we should do it in the entire declaration.
                fun_decl.node.sig.params = fun_decl
                    .node
                    .sig
                    .params
                    .into_iter()
                    .map(|(param, param_ty)| {
                        (
                            param,
                            param_ty.map(|ty| ty.subst_var(&trait_ty_param, &impl_decl.ty.node)),
                        )
                    })
                    .collect();

                impl_decl.items.push(fun_decl.map(ast::ImplDeclItem::Fun));
            }
        }

        tys.exit_scope();
        assert_eq!(tys.len_scopes(), 1);
    }

    // Check bounds of trait type parameters.
    // This needs to be done after populating the trait->implementing types map, as we use the map
    // to check if a type satisfies the bounds.
    for decl in module {
        let impl_decl = match &mut decl.node {
            ast::TopDecl::Impl(impl_decl) => &mut impl_decl.node,
            _ => continue,
        };

        let trait_con_id = match &impl_decl.trait_ {
            Some(trait_id) => &trait_id.node,
            None => continue,
        };

        tys.enter_scope();

        let _impl_context = convert_and_bind_context(
            &mut tys,
            &impl_decl.context,
            TyVarConversion::ToQVar,
            &decl.loc,
        );

        let trait_ty_con = tys.get_con(trait_con_id).unwrap();

        let trait_ty_params = &trait_ty_con.ty_params;
        assert_eq!(trait_ty_params.len(), 1);

        let impl_ty = convert_ast_ty(&tys, &impl_decl.ty.node, &impl_decl.ty.loc);
        let (impl_ty_con_id, _) = impl_ty.con(tys.cons()).unwrap();

        // TODO: What do we need to check on associated types here?
        for (bound, _assoc_tys) in &trait_ty_params[0].1 {
            let bound_trait_details = tys.get_con(bound).unwrap().trait_details().unwrap();
            if !bound_trait_details
                .implementing_tys
                .contains(&impl_ty_con_id)
            {
                panic!(
                    "{}: Type {} does not implement {}",
                    loc_display(&decl.loc),
                    impl_ty_con_id,
                    bound
                );
            }
        }

        for item in &impl_decl.items {
            if let ast::ImplDeclItem::AssocTy(ast::AssocTyDecl { name, ty }) = &item.node {
                let ty = convert_ast_ty(&tys, &ty.node, &ty.loc);
                let old = tys
                    .get_con_mut(&impl_ty_con_id)
                    .unwrap()
                    .assoc_tys
                    .insert(name.clone(), ty);
                if old.is_some() {
                    panic!(
                        "{}: Associated type {} is defined multiple times for type {}",
                        loc_display(&item.loc),
                        name,
                        impl_ty_con_id
                    );
                }
            }
        }

        tys.exit_scope();
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
    Map<Id, Map<Id, Scheme>>,
) {
    let mut top_schemes: Map<Id, Scheme> = Default::default();
    let mut associated_fn_schemes: Map<Id, Map<Id, Scheme>> = Default::default();
    let mut method_schemes: Map<Id, Map<Id, Scheme>> = Default::default();

    for decl in module {
        // New scope for type and function contexts.
        assert_eq!(tys.len_scopes(), 1);
        tys.enter_scope();

        match &decl.node {
            ast::TopDecl::Fun(ast::L {
                node: ast::FunDecl { sig, body: _ },
                loc,
            }) => {
                let fun_context =
                    convert_and_bind_context(tys, &sig.type_params, TyVarConversion::ToQVar, loc);

                let arg_tys: Vec<Ty> = sig
                    .params
                    .iter()
                    .map(|(_name, ty)| convert_ast_ty(tys, &ty.node, &ty.loc))
                    .collect();

                let ret_ty: Ty = match &sig.return_ty {
                    Some(ret_ty) => convert_ast_ty(tys, &ret_ty.node, &ret_ty.loc),
                    None => Ty::unit(),
                };

                let fun_ty = Ty::Fun(arg_tys, Box::new(ret_ty));

                let scheme = Scheme {
                    quantified_vars: fun_context,
                    ty: fun_ty,
                    loc: loc.clone(),
                };

                let old = top_schemes.insert(sig.name.node.clone(), scheme);
                if old.is_some() {
                    panic!(
                        "{}: Function {} is defined multiple times",
                        loc_display(loc),
                        sig.name.node
                    );
                }
            }

            ast::TopDecl::Impl(impl_decl) => {
                let impl_context = convert_and_bind_context(
                    tys,
                    &impl_decl.node.context,
                    TyVarConversion::ToQVar,
                    &impl_decl.loc,
                );

                let self_ty: Ty =
                    convert_ast_ty(tys, &impl_decl.node.ty.node, &impl_decl.node.ty.loc);

                tys.insert_con(
                    "Self".into(),
                    TyCon {
                        id: "Self".into(),
                        ty_params: vec![],
                        assoc_tys: Default::default(),
                        details: TyConDetails::Synonym(self_ty.clone()),
                    },
                );

                let (self_ty_con_id, _) = self_ty.con(tys.cons()).unwrap();

                bind_associated_types(impl_decl, tys);

                for item in &impl_decl.node.items {
                    let fun = match &item.node {
                        ast::ImplDeclItem::AssocTy(_) => continue,
                        ast::ImplDeclItem::Fun(fun) => fun,
                    };

                    assert_eq!(tys.len_scopes(), 2); // top-level, impl
                    tys.enter_scope();

                    let sig = &fun.sig;

                    let fun_context = convert_and_bind_context(
                        tys,
                        &sig.type_params,
                        TyVarConversion::ToQVar,
                        &item.loc,
                    );

                    if sig.self_ {
                        tys.insert_var(SmolStr::new_static("self"), self_ty.clone());
                    }

                    let mut arg_tys: Vec<Ty> = sig
                        .params
                        .iter()
                        .map(|(_name, ty)| convert_ast_ty(tys, &ty.node, &ty.loc))
                        .collect();

                    if sig.self_ {
                        arg_tys.insert(0, self_ty.clone());
                    }

                    let ret_ty: Ty = match &sig.return_ty {
                        Some(ret_ty) => convert_ast_ty(tys, &ret_ty.node, &ret_ty.loc),
                        None => Ty::unit(),
                    };

                    let fun_ty = Ty::Fun(arg_tys, Box::new(ret_ty));

                    let scheme = Scheme {
                        quantified_vars: impl_context
                            .iter()
                            .cloned()
                            .chain(fun_context.into_iter())
                            .collect(),
                        ty: fun_ty,
                        loc: item.loc.clone(),
                    };

                    if sig.self_ {
                        let old = method_schemes
                            .entry(self_ty_con_id.clone())
                            .or_default()
                            .insert(fun.sig.name.node.clone(), scheme.clone());

                        // Add the type key to associated_fn_schemes to make lookups easier.
                        associated_fn_schemes
                            .entry(self_ty_con_id.clone())
                            .or_default();

                        if old.is_some() {
                            panic!(
                                "{}: Method {} for type {} is defined multiple times",
                                loc_display(&item.loc),
                                fun.sig.name.node,
                                self_ty_con_id
                            );
                        }
                    } else {
                        let old = associated_fn_schemes
                            .entry(self_ty_con_id.clone())
                            .or_default()
                            .insert(fun.sig.name.node.clone(), scheme.clone());

                        method_schemes.entry(self_ty_con_id.clone()).or_default();

                        if old.is_some() {
                            panic!(
                                "{}: Associated function {} for type {} is defined multiple times",
                                loc_display(&item.loc),
                                fun.sig.name.node,
                                self_ty_con_id
                            );
                        }
                    }

                    tys.exit_scope();
                    assert_eq!(tys.len_scopes(), 2); // top-level, impl

                    // If this is a trait method, check that the type matches the method type in
                    // the trait.
                    if let Some(trait_id) = &impl_decl.node.trait_ {
                        let trait_ty_con = tys.cons().get(&trait_id.node).unwrap();
                        let trait_details = trait_ty_con.trait_details().unwrap();

                        let fun_name: &Id = &fun.sig.name.node;

                        let trait_fun_scheme = &trait_details
                            .methods
                            .get(fun_name)
                            .unwrap_or_else(|| {
                                panic!(
                                    "{}: Trait {} does not have a method named {}",
                                    loc_display(&item.loc),
                                    trait_ty_con.id,
                                    fun_name
                                )
                            })
                            .scheme;

                        let trait_ty_param = &trait_ty_con.ty_params[0].0;

                        // Type of the method in the trait declaration, with `self` type substituted for the
                        // type implementing the trait.
                        let mut trait_fun_scheme = trait_fun_scheme
                            .subst(trait_ty_param, &self_ty, &item.loc)
                            .subst_self(&self_ty);

                        // Also add quantified variables of `impl`.
                        trait_fun_scheme
                            .quantified_vars
                            .splice(0..0, impl_context.iter().cloned());

                        if !trait_fun_scheme.eq_modulo_alpha(
                            tys.cons(),
                            &Default::default(),
                            &scheme,
                            &item.loc,
                        ) {
                            panic!(
                                "{}: Trait method implementation of {} does not match the trait method type
                                Trait method type:          {}
                                Implementation method type: {}",
                                loc_display(&item.loc),
                                fun_name,
                                trait_fun_scheme,
                                scheme
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
                                Some(ConFields::Unnamed(tys)) => {
                                    Ty::Fun(tys, Box::new(ret.clone()))
                                }
                                Some(ConFields::Named(tys)) => {
                                    Ty::FunNamedArgs(tys, Box::new(ret.clone()))
                                }
                            };
                            let scheme = Scheme {
                                quantified_vars: ty_decl
                                    .node
                                    .type_params
                                    .iter()
                                    .map(|ty_param| (ty_param.clone(), Default::default()))
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
                            Some(ConFields::Unnamed(tys)) => Ty::Fun(tys, Box::new(ret.clone())),
                            Some(ConFields::Named(tys)) => {
                                Ty::FunNamedArgs(tys, Box::new(ret.clone()))
                            }
                        };
                        let scheme = Scheme {
                            quantified_vars: ty_decl
                                .node
                                .type_params
                                .iter()
                                .map(|ty_param| (ty_param.clone(), Default::default()))
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

            ast::TopDecl::Trait(_) | ast::TopDecl::Import(_) => {
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

    let scheme = tys
        .top_schemes
        .get(&fun.node.sig.name.node)
        .unwrap()
        .clone();

    assert_eq!(tys.tys.len_scopes(), 1);
    tys.tys.enter_scope();

    let fn_bounds = convert_and_bind_context(
        &mut tys.tys,
        &fun.node.sig.type_params,
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

    let mut preds: PredSet = Default::default();

    let context = scheme.quantified_vars.iter().cloned().collect();

    let mut tc_state = TcFunState {
        context: &context,
        return_ty: &ret_ty,
        env: &mut env,
        var_gen: &mut var_gen,
        tys,
        preds: &mut preds,
    };

    if let Some(body) = &mut fun.node.body.as_mut() {
        check_stmts(&mut tc_state, &mut body.node, Some(&ret_ty), 0, 0);

        for stmt in &mut body.node {
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
    let impl_bounds = convert_and_bind_context(
        &mut tys.tys,
        &impl_.node.context,
        TyVarConversion::ToOpaque,
        &impl_.loc,
    );

    // Schemes overridden by trait bounds.
    let old_schemes_1 = bind_type_params(&impl_bounds, tys, &impl_.loc);

    let trait_ty = convert_ast_ty(&tys.tys, &impl_.node.ty.node, &impl_.loc);
    let (ty_con_id, ty_args) = trait_ty.con(tys.tys.cons()).unwrap();

    // Bind associated types.
    bind_associated_types(impl_, &mut tys.tys);

    let ty_con = tys.tys.get_con(&ty_con_id).unwrap().clone();

    if let Some(trait_details) = ty_con.trait_details() {
        let mut ty_args = match ty_args {
            TyArgs::Positional(ty_args) => ty_args,
            TyArgs::Named(_) => panic!("Trait type parameter cannot be named"),
        };

        assert_eq!(ty_args.len(), 1); // checked in the previous pass
        assert_eq!(ty_con.ty_params.len(), 1); // checked in the previous pass

        let self_ty = ty_args.pop().unwrap();

        tys.tys.insert_con(
            "Self".into(),
            TyCon {
                id: "Self".into(),
                ty_params: vec![],
                assoc_tys: Default::default(),
                details: TyConDetails::Synonym(self_ty.clone()),
            },
        );

        // Check method bodies.
        for item in &mut impl_.node.items {
            let fun = match &mut item.node {
                ast::ImplDeclItem::AssocTy(_) => continue,
                ast::ImplDeclItem::Fun(fun) => fun,
            };

            tys.tys.enter_scope();

            // Bind function type parameters.
            let fn_bounds = convert_and_bind_context(
                &mut tys.tys,
                &fun.sig.type_params,
                TyVarConversion::ToOpaque,
                &impl_.loc,
            );

            // Schemes overridden by method bounds.
            let old_schemes_2 = bind_type_params(&fn_bounds, tys, &item.loc);

            // Check the body.
            if let Some(body) = &mut fun.body {
                let ret_ty = match &fun.sig.return_ty {
                    Some(ty) => convert_ast_ty(&tys.tys, &ty.node, &ty.loc),
                    None => Ty::unit(),
                };

                let mut preds: PredSet = Default::default();
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

                let mut tc_state = TcFunState {
                    context: &context,
                    return_ty: &ret_ty,
                    env: &mut env,
                    var_gen: &mut var_gen,
                    tys,
                    preds: &mut preds,
                };

                check_stmts(&mut tc_state, &mut body.node, Some(&ret_ty), 0, 0);

                for stmt in &mut body.node {
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
        for item in &impl_.node.items {
            let fun_decl = match &item.node {
                ast::ImplDeclItem::AssocTy(_) => continue,
                ast::ImplDeclItem::Fun(fun_decl) => fun_decl,
            };
            let fun_id = &fun_decl.sig.name.node;
            match (
                trait_method_ids.contains(fun_id),
                implemented_method_ids.contains(fun_id),
            ) {
                (true, true) => panic!(
                    "{}: Trait method {} implemented multiple times",
                    loc_display(&item.loc),
                    fun_id
                ),

                (true, false) => {
                    implemented_method_ids.insert(fun_id);
                }

                (false, _) => {
                    panic!(
                        "{}: Trait {} does not have method {}",
                        loc_display(&item.loc),
                        ty_con_id,
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
    } else {
        for item in &mut impl_.node.items {
            let fun = match &mut item.node {
                ast::ImplDeclItem::AssocTy(_) => continue,
                ast::ImplDeclItem::Fun(fun) => fun,
            };

            assert_eq!(tys.tys.len_scopes(), 2); // top-level, impl
            tys.tys.enter_scope();

            // Bind function type parameters.
            let fn_bounds = convert_and_bind_context(
                &mut tys.tys,
                &fun.sig.type_params,
                TyVarConversion::ToOpaque,
                &item.loc,
            );

            // Schemes overridden by method bounds.
            let old_schemes_2 = bind_type_params(&fn_bounds, tys, &item.loc);

            // Check the body.
            if let Some(body) = &mut fun.body {
                let ret_ty = match &fun.sig.return_ty {
                    Some(ty) => convert_ast_ty(&tys.tys, &ty.node, &ty.loc),
                    None => Ty::unit(),
                };

                let mut preds: PredSet = Default::default();
                let mut env: ScopeMap<Id, Ty> = ScopeMap::default();
                let mut var_gen = TyVarGen::default();

                env.insert(SmolStr::new_static("self"), trait_ty.clone());

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

                let mut tc_state = TcFunState {
                    context: &context,
                    return_ty: &ret_ty,
                    env: &mut env,
                    var_gen: &mut var_gen,
                    tys,
                    preds: &mut preds,
                };

                check_stmts(&mut tc_state, &mut body.node, Some(&ret_ty), 0, 0);

                for stmt in &mut body.node {
                    normalize_instantiation_types(&mut stmt.node, tys.tys.cons());
                }

                resolve_all_preds(&context, tys, preds, &mut var_gen, 0);
            }

            unbind_type_params(old_schemes_2, &mut tys.method_schemes);

            tys.tys.exit_scope();
            assert_eq!(tys.tys.len_scopes(), 2); // top-level, impl
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
    context: &Map<Id, Map<Id, Map<Id, Ty>>>,
    tys: &PgmTypes,
    preds: PredSet,
    var_gen: &mut TyVarGen,
    level: u32,
) -> PredSet {
    let mut remaining_preds: PredSet = Default::default();

    for Pred {
        ty_var,
        trait_,
        assoc_tys,
        loc,
    } in preds.into_preds()
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
                    && context.get(con).map(|ctx| ctx.contains_key(&trait_)) != Some(true)
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
            | Ty::Record { .. }
            | Ty::Variant { .. }
            | Ty::Fun(_, _)
            | Ty::FunNamedArgs(_, _)
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
}

fn resolve_all_preds(
    context: &Map<Id, Map<Id, Map<Id, Ty>>>,
    tys: &PgmTypes,
    preds: PredSet,
    var_gen: &mut TyVarGen,
    level: u32,
) {
    let unresolved_preds = resolve_preds(context, tys, preds, var_gen, level);
    report_unresolved_preds(unresolved_preds, tys.tys.cons());
}

fn report_unresolved_preds(preds: PredSet, cons: &ScopeMap<Id, TyCon>) {
    let preds = preds.into_preds();

    if preds.is_empty() {
        return;
    }

    for Pred {
        ty_var,
        trait_,
        assoc_tys: _,
        loc,
    } in preds
    {
        eprintln!(
            "{}: Type {} does not implement trait {}",
            loc_display(&loc),
            ty_var.normalize(cons),
            trait_
        );
    }

    panic!();
}

fn bind_associated_types(impl_decl: &ast::L<ast::ImplDecl>, tys: &mut TyMap) {
    // TODO: To allow RHSs refer to associated types, bind associated types to
    // placeholder first, then as type synonyms to their RHSs.
    for item in &impl_decl.node.items {
        let (assoc_ty_id, ty) = match &item.node {
            ast::ImplDeclItem::AssocTy(ast::AssocTyDecl { name, ty }) => (name, ty),
            ast::ImplDeclItem::Fun(_) => continue,
        };

        let ty_converted = convert_ast_ty(tys, &ty.node, &ty.loc);

        // TODO: Check that the type has kind `*`.
        tys.insert_con(
            assoc_ty_id.clone(),
            TyCon {
                id: assoc_ty_id.clone(),
                ty_params: vec![],
                assoc_tys: Default::default(),
                details: TyConDetails::Synonym(ty_converted),
            },
        );
    }
}

fn bind_type_params(
    params: &[(Id, Map<Id, Map<Id, Ty>>)],
    tys: &mut PgmTypes,
    loc: &ast::Loc,
) -> Map<SmolStr, Option<Map<SmolStr, Scheme>>> {
    let mut old_method_schemes: Map<Id, Option<Map<Id, Scheme>>> = Default::default();

    for (var, bounds) in params {
        old_method_schemes.insert(var.clone(), tys.method_schemes.remove(var));

        for (trait_, assoc_tys) in bounds {
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

                tys.method_schemes.entry(var.clone()).or_default().insert(
                    method_id.clone(),
                    method_scheme.subst_self(&Ty::Con(var.clone())),
                );
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
