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
                for item in &mut node.items {
                    match &mut item.node {
                        ast::TraitDeclItem::AssocTy(_) => {}
                        ast::TraitDeclItem::Fun(fun) => {
                            if fun.sig.exceptions.is_none() {
                                fun.sig.exceptions = Some(exn_type());
                            }
                        }
                    }
                }
            }

            ast::TopDecl::Impl(ast::L { node, .. }) => {
                for item in &mut node.items {
                    match &mut item.node {
                        ast::ImplDeclItem::AssocTy(_) => {}
                        ast::ImplDeclItem::Fun(fun) => {
                            if fun.sig.exceptions.is_none() {
                                fun.sig.exceptions = Some(exn_type());
                            }
                        }
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

    /// The full context of the function, including `impl` context. E.g. in
    /// ```ignore
    /// impl[t: P1] A[t]:
    ///     fn f[a: P2](self, a: a)
    /// ```
    /// this will be `{t => {P1}, a => {P2}}`.
    ///
    /// This is used to eagerly resolve predicates during type checking, to be able to resolve
    /// associated types.
    context: &'a Map<Id, QVar>,

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
    preds: &'a mut PredSet,
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
                let ty_params = vec![trait_decl.node.ty.id.clone()];
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
                            .map(|ty| (ty.node, Default::default()))
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

                let trait_context_ast: ast::Context = vec![trait_decl.node.ty.clone()];

                let trait_var_kinds: Map<Id, Kind> =
                    [(trait_decl.node.ty.id.node.clone(), Kind::Star)]
                        .into_iter()
                        .collect();

                let trait_context: Vec<(Id, QVar)> = convert_and_bind_context(
                    &mut tys,
                    &trait_context_ast,
                    &trait_var_kinds,
                    TyVarConversion::ToQVar,
                    &trait_decl.loc,
                );

                // Convert bounds before binding associated types and self.
                let bounds: Map<Id, Map<Id, Ty>> = trait_decl
                    .node
                    .ty
                    .bounds
                    .iter()
                    .map(|bound| convert_bound(&tys, bound))
                    .collect();

                // E.g. `t` in `trait Debug[t]: ...`.
                let self_ty_id: Id = trait_decl.node.ty.id.node.clone();

                // The `QVar` for `t` in the example. `t` will be mapped to this when converting
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
                            ty: Box::new(self_ty.clone()),
                            assoc_ty: assoc_ty.clone(),
                        },
                    );
                }

                let methods: Map<Id, TraitMethod> = trait_decl
                    .node
                    .items
                    .iter()
                    .filter_map(|item| match &item.node {
                        ast::TraitDeclItem::AssocTy(_) => None,
                        ast::TraitDeclItem::Fun(fun) => {
                            // New scope for function context.
                            tys.enter_scope();

                            let mut fun_var_kinds: Map<Id, Kind> = trait_var_kinds.clone();
                            fun_var_kinds.extend(fun_sig_ty_var_kinds(&fun.sig));

                            let fun_context: Vec<(Id, QVar)> = convert_and_bind_context(
                                &mut tys,
                                &fun.sig.type_params,
                                &fun_var_kinds,
                                TyVarConversion::ToQVar,
                                &item.loc,
                            );

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

                            let exceptions = match &fun.sig.exceptions {
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
                                quantified_vars: trait_context
                                    .iter()
                                    .map(|(qvar, details)| (qvar.clone(), details.clone()))
                                    .chain(fun_context.into_iter())
                                    .collect(),
                                ty: fun_ty,
                                loc: item.loc.clone(),
                            };

                            Some((fun.name.node.clone(), {
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

        let impl_var_kinds: Map<Id, Kind> = impl_decl
            .context
            .iter()
            .map(|param| (param.id.node.clone(), Kind::Star))
            .collect();

        let _impl_context = convert_and_bind_context(
            &mut tys,
            &impl_decl.context,
            &impl_var_kinds,
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
        let mut defined_assoc_tys: Map<Id, ast::Type> = Default::default();
        for item in &impl_decl.items {
            if let ast::ImplDeclItem::AssocTy(impl_assoc_ty) = &item.node {
                let old = defined_assoc_tys
                    .insert(impl_assoc_ty.name.clone(), impl_assoc_ty.ty.node.clone());
                if old.is_some() {
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
        let defined_assoc_tys_: Set<Id> = defined_assoc_tys.keys().cloned().collect();
        if &defined_assoc_tys_ != trait_assoc_tys {
            let extras: Set<&Id> = defined_assoc_tys_.difference(trait_assoc_tys).collect();
            if !extras.is_empty() {
                panic!(
                    "{}: Extra associated types defined: {:?}",
                    loc_display(&decl.loc),
                    extras
                );
            }

            let missing: Set<&Id> = trait_assoc_tys.difference(&defined_assoc_tys_).collect();
            if !missing.is_empty() {
                panic!(
                    "{}: Missing associated types: {:?}",
                    loc_display(&decl.loc),
                    missing
                );
            }
        }

        // Type parameter of the trait, e.g. `t` in `trait Debug[t]: ...`.
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
                ast::ImplDeclItem::Fun(fun) => &fun.name.node == method,
            }) {
                continue;
            }

            if method_decl.fun_decl.node.body.is_some() {
                let mut fun_decl = method_decl.fun_decl.clone();

                let mut substs: Map<Id, ast::Type> = Default::default();
                substs.insert(trait_ty_param.clone(), impl_decl.ty.node.clone());
                substs.extend(defined_assoc_tys.clone());

                // TODO: For now we only replace trait type param with self in the signature, but
                // we should do it in the entire declaration.

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

        let impl_var_kinds: Map<Id, Kind> = impl_decl
            .context
            .iter()
            .map(|param| (param.id.node.clone(), Kind::Star))
            .collect();

        let _impl_context = convert_and_bind_context(
            &mut tys,
            &impl_decl.context,
            &impl_var_kinds,
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
                node: ast::FunDecl { name, sig, body: _ },
                loc,
            }) => {
                let fun_var_kinds = fun_sig_ty_var_kinds(sig);

                let fun_context: Vec<(Id, QVar)> = convert_and_bind_context(
                    tys,
                    &sig.type_params,
                    &fun_var_kinds,
                    TyVarConversion::ToQVar,
                    loc,
                );

                let arg_tys: Vec<Ty> = sig
                    .params
                    .iter()
                    .map(|(_name, ty)| convert_ast_ty(tys, &ty.node, &ty.loc))
                    .collect();

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
                    quantified_vars: fun_context,
                    ty: fun_ty,
                    loc: loc.clone(),
                };

                let old = top_schemes.insert(name.node.clone(), scheme);
                if old.is_some() {
                    panic!(
                        "{}: Function {} is defined multiple times",
                        loc_display(loc),
                        name.node
                    );
                }
            }

            ast::TopDecl::Impl(impl_decl) => {
                let impl_var_kinds: Map<Id, Kind> = impl_decl
                    .node
                    .context
                    .iter()
                    .map(|param| (param.id.node.clone(), Kind::Star))
                    .collect();

                let impl_context: Vec<(Id, QVar)> = convert_and_bind_context(
                    tys,
                    &impl_decl.node.context,
                    &impl_var_kinds,
                    TyVarConversion::ToQVar,
                    &impl_decl.loc,
                );

                let self_ty: Ty =
                    convert_ast_ty(tys, &impl_decl.node.ty.node, &impl_decl.node.ty.loc);

                let (self_ty_con_id, _) = self_ty.con(tys.cons()).unwrap();

                // If not in a trait impl block, make sure `self` is not a trait.
                if impl_decl.node.trait_.is_none()
                    && tys.cons().get(&self_ty_con_id).map(|con| con.is_trait()) == Some(true)
                {
                    panic!(
                        "{}: Type constructor {} in trait `impl` block is not a trait",
                        loc_display(&impl_decl.loc),
                        self_ty_con_id
                    );
                }

                bind_associated_types(impl_decl, tys);

                for item in &impl_decl.node.items {
                    let fun = match &item.node {
                        ast::ImplDeclItem::AssocTy(_) => continue,
                        ast::ImplDeclItem::Fun(fun) => fun,
                    };

                    assert_eq!(tys.len_scopes(), 2); // top-level, impl
                    tys.enter_scope();

                    let sig = &fun.sig;

                    let mut fun_var_kinds = impl_var_kinds.clone();
                    fun_var_kinds.extend(fun_sig_ty_var_kinds(sig));

                    let fun_context = convert_and_bind_context(
                        tys,
                        &sig.type_params,
                        &fun_var_kinds,
                        TyVarConversion::ToQVar,
                        &item.loc,
                    );

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

                    let exceptions = match &fun.sig.exceptions {
                        Some(ty) => convert_ast_ty(tys, &ty.node, &ty.loc),
                        None => panic!(),
                    };

                    let fun_ty = Ty::Fun {
                        args: FunArgs::Positional(arg_tys),
                        ret: Box::new(ret_ty),
                        exceptions: Some(Box::new(exceptions)),
                    };

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
                            .insert(fun.name.node.clone(), scheme.clone());

                        if old.is_some() {
                            panic!(
                                "{}: Method {} for type {} is defined multiple times",
                                loc_display(&item.loc),
                                fun.name.node,
                                self_ty_con_id
                            );
                        }
                    } else {
                        let old = associated_fn_schemes
                            .entry(self_ty_con_id.clone())
                            .or_default()
                            .insert(fun.name.node.clone(), scheme.clone());

                        if old.is_some() {
                            panic!(
                                "{}: Associated function {} for type {} is defined multiple times",
                                loc_display(&item.loc),
                                fun.name.node,
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

                        let fun_name: &Id = &fun.name.node;

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

                        // Type of the method in the trait declaration, with the self type substituted for the
                        // type implementing the trait.
                        let mut trait_fun_scheme =
                            trait_fun_scheme.subst(trait_ty_param, &self_ty, &item.loc);

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

    let mut preds: PredSet = Default::default();

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
            for item in &mut impl_.node.items {
                let fun = match &mut item.node {
                    ast::ImplDeclItem::AssocTy(_) => continue,
                    ast::ImplDeclItem::Fun(fun) => fun,
                };

                tys.tys.enter_scope();

                // Bind function type parameters.
                let var_kinds = fun_sig_ty_var_kinds(&fun.sig);
                let fn_bounds = convert_and_bind_context(
                    &mut tys.tys,
                    &fun.sig.type_params,
                    &var_kinds,
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
            for item in &impl_.node.items {
                let fun_decl = match &item.node {
                    ast::ImplDeclItem::AssocTy(_) => continue,
                    ast::ImplDeclItem::Fun(fun_decl) => fun_decl,
                };
                let fun_id = &fun_decl.name.node;
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
            for item in &mut impl_.node.items {
                let fun = match &mut item.node {
                    ast::ImplDeclItem::AssocTy(_) => continue,
                    ast::ImplDeclItem::Fun(fun) => fun,
                };

                assert_eq!(tys.tys.len_scopes(), 2); // top-level, impl
                tys.tys.enter_scope();

                // Bind function type parameters.
                let var_kinds = fun_sig_ty_var_kinds(&fun.sig);
                let fn_bounds: Vec<(Id, QVar)> = convert_and_bind_context(
                    &mut tys.tys,
                    &fun.sig.type_params,
                    &var_kinds,
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

                    env.insert(SmolStr::new_static("self"), self_ty.clone());

                    for (param_name, param_ty) in &fun.sig.params {
                        env.insert(
                            param_name.clone(),
                            convert_ast_ty(&tys.tys, &param_ty.node, &item.loc),
                        );
                    }

                    let context = impl_bounds
                        .iter()
                        .map(|(qvar, details)| (qvar.clone(), details.clone()))
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
}

fn resolve_all_preds(
    context: &Map<Id, QVar>,
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
