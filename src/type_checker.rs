#![allow(clippy::mutable_key_type)]

mod convert;
mod expr;
mod pat;
mod stmt;
mod ty;
mod ty_map;
mod unification;

use convert::convert_fields;
pub use convert::*;
use stmt::check_stmts;
use ty::*;
pub use ty::{Id, TyArgs};
use ty_map::TyMap;

use crate::ast;
use crate::collections::{Map, ScopeMap, Set};

use smol_str::SmolStr;

/// Type constructors and types in the program.
#[derive(Debug)]
pub struct PgmTypes {
    /// Type schemes of top-level values.
    pub top_schemes: Map<Id, Scheme>,

    /// Type schemes of associated functions.
    pub associated_schemes: Map<Id, Map<Id, Scheme>>,

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
        match &decl.node {
            ast::TopDecl::Import(_) => panic!(
                "{}: Import declaration in check_module",
                loc_string(&decl.loc)
            ),

            // Types and schemes added to `PgmTypes` by `collect_types`.
            ast::TopDecl::Type(_) | ast::TopDecl::Trait(_) => {}

            ast::TopDecl::Impl(impl_) => check_impl(impl_, &mut tys),

            ast::TopDecl::Fun(fun) => check_top_fun(fun, &mut tys),
        }
    }

    tys
}

/// Collect type constructors (traits and data) and type schemes (top-level, associated, traits) of
/// the program.
///
/// Does not type check the code, only collects types and type schemes.
fn collect_types(module: &mut ast::Module) -> PgmTypes {
    let mut tys = collect_cons(module);
    let (top_schemes, associated_schemes) = collect_schemes(module, &mut tys);
    PgmTypes {
        top_schemes,
        associated_schemes,
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
                    panic!("Type {} is defined multiple times", ty_name);
                }
                tys.insert_con(
                    ty_name.clone(),
                    TyCon {
                        id: ty_name.clone(),
                        ty_params: ty_params.into_iter().map(|ty| (ty, vec![])).collect(),
                        assoc_tys: Default::default(),
                        details: TyConDetails::placeholder(),
                    },
                );
            }

            ast::TopDecl::Trait(trait_decl) => {
                let ty_name = trait_decl.node.name.node.clone();
                let ty_params = vec![trait_decl.node.ty.node.0.clone()];
                if tys.has_con(&ty_name) {
                    panic!("Type {} is defined multiple times", ty_name);
                }
                tys.insert_con(
                    ty_name.clone(),
                    TyCon {
                        id: ty_name.clone(),
                        ty_params: ty_params.into_iter().map(|ty| (ty, vec![])).collect(),
                        assoc_tys: Default::default(),
                        details: TyConDetails::placeholder(),
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
                            let cons: Vec<Id> = sum_cons
                                .iter()
                                .map(|ast::ConstructorDecl { name, fields: _ }| name.clone())
                                .collect();

                            TyConDetails::Type(TypeDetails { cons })
                        }

                        ast::TypeDeclRhs::Product(_fields) => TyConDetails::Type(TypeDetails {
                            cons: vec![ty_decl.node.name.clone()],
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
                let bounds: Vec<Ty> = trait_decl
                    .node
                    .ty
                    .node
                    .1
                    .iter()
                    .map(|ty| convert_ast_ty(&tys, &ty.node, &ty.loc))
                    .collect();

                // E.g. `T` in `trait Debug[T]: ...`.
                let self_ty_id: Id = trait_decl.node.ty.node.0.clone();

                // The `QVar` for `T` in the example. `T` will be mapped to this when converting
                // types.
                let self_ty = Ty::QVar(self_ty_id.clone());

                // Bind assocaited types.
                let assoc_tys: Vec<&Id> = trait_decl
                    .node
                    .items
                    .iter()
                    .filter_map(|item| match &item.node {
                        ast::TraitDeclItem::AssocTy(ty) => Some(ty),
                        ast::TraitDeclItem::Fun(_) => None,
                    })
                    .collect();

                for assoc_ty in &assoc_tys {
                    tys.insert_con((*assoc_ty).clone(), TyCon::opaque((*assoc_ty).clone()));
                    tys.insert_var((*assoc_ty).clone(), Ty::Con((*assoc_ty).clone()));
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
                    implementing_tys: Default::default(),
                });

                tys.exit_scope();
                assert_eq!(tys.len_scopes(), 1);
            }

            ast::TopDecl::Fun(_) | ast::TopDecl::Import(_) | ast::TopDecl::Impl(_) => continue,
        }
    }

    // Add default methods to impls, and populate the trait->implementing types map.
    //
    // We don't need to type check default methods copied to impls, but for now we do. So replace
    // the trait type parameter with the self type in the copied declarations.
    for decl in module.iter_mut() {
        let impl_decl = match &mut decl.node {
            ast::TopDecl::Impl(impl_decl) => &mut impl_decl.node,
            _ => continue,
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

        let (trait_con_id, trait_con_args) = match impl_ty.con(tys.cons()) {
            Some(con_and_args) => con_and_args,
            None => {
                tys.exit_scope();
                continue;
            }
        };

        let trait_con_args = match trait_con_args {
            TyArgs::Positional(args) => args,
            TyArgs::Named(_) => panic!(), // can't happen, should be checked earlier?
        };

        let trait_ty_con = tys.get_con_mut(&trait_con_id).unwrap();

        let (trait_methods, trait_implementing_tys) = match &mut trait_ty_con.details {
            TyConDetails::Trait(TraitDetails {
                ref mut methods,
                ref mut implementing_tys,
            }) => (methods, implementing_tys),
            TyConDetails::Type { .. } | TyConDetails::Synonym(_) => {
                tys.exit_scope();
                continue;
            }
        };

        assert_eq!(trait_con_args.len(), 1);
        assert_eq!(trait_ty_con.ty_params.len(), 1);

        // Type parameter of the trait, e.g. `T` in `trait Debug[T]: ...`.
        let trait_ty_param: Id = trait_ty_con.ty_params[0].0.clone();

        // Type constructor of the type implementing the trait.
        // TODO: We are passing empty con map here to avoid borrow checking issues. This will fail
        // when the trait arugment is a type synonym, which we should reject anyway, but with a
        // proper error message.
        let (self_ty_con, _) = trait_con_args[0].con(&Default::default()).unwrap();

        if !trait_implementing_tys.insert(self_ty_con.clone()) {
            panic!(
                "{}: Trait {} is implemented for type {} multiple times",
                loc_string(&decl.loc),
                trait_con_id,
                self_ty_con
            );
        }

        // The self type, e.g. in `Iterator[VecIter[T]]`, this is `VecIter[T]`. AST type instead of
        // type checking type to be able to substitute the self type for the type parameter of the
        // trait in default methods.
        let self_ast_ty = match &impl_decl.ty.node {
            ast::Type::Named(ast::NamedType { name: _, args }) => {
                assert_eq!(args.len(), 1);
                assert!(args[0].node.0.is_none()); // type parameter shouldn't be named
                args[0].node.1.clone()
            }
            ast::Type::Record(_) | ast::Type::AssocType { .. } => panic!(), // can't happen
        };

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
                            param_ty.map(|ty| ty.subst_var(&trait_ty_param, &self_ast_ty.node)),
                        )
                    })
                    .collect();

                impl_decl.items.push(fun_decl.map(ast::ImplDeclItem::Fun));
            }
        }

        tys.exit_scope();
        assert_eq!(tys.len_scopes(), 1);
    }

    assert_eq!(tys.len_scopes(), 1);
    tys
}

// `ty_cons` is mut to be able to update it with associated types when checking traits.
fn collect_schemes(
    module: &ast::Module,
    tys: &mut TyMap,
) -> (Map<Id, Scheme>, Map<Id, Map<Id, Scheme>>) {
    let mut top_schemes: Map<Id, Scheme> = Default::default();
    let mut associated_schemes: Map<Id, Map<Id, Scheme>> = Default::default();

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
                        loc_string(loc),
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

                let mut self_ty: Ty =
                    convert_ast_ty(tys, &impl_decl.node.ty.node, &impl_decl.node.ty.loc);

                let (mut ty_con_id, ty_args) = self_ty.con(tys.cons()).unwrap();
                let ty_con = match tys.get_con(&ty_con_id) {
                    Some(ty_con) => ty_con,
                    None => panic!("{}: Unknown type {}", loc_string(&impl_decl.loc), ty_con_id),
                };

                if ty_con.is_trait() {
                    let mut ty_args = match ty_args {
                        TyArgs::Positional(args) => args,
                        TyArgs::Named(_) => panic!(), // should've been checked in collect_cons
                    };

                    assert_eq!(ty_args.len(), 1); // should've been checked in collect_cons

                    // Add the associated method to the type rather than to the trait.
                    self_ty = ty_args.pop().unwrap();
                    let (ty_con_id_, _) = self_ty.con(tys.cons()).unwrap_or_else(|| {
                        panic!(
                            "{}: Trait type argument needs to be a type constructor, but it is {:?}",
                            loc_string(&impl_decl.loc),
                            self_ty
                        )
                    });
                    ty_con_id = ty_con_id_;

                    bind_associated_types(impl_decl, tys);

                    // TODO: Check that the method types match trait methods.
                }

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

                    let old = associated_schemes
                        .entry(ty_con_id.clone())
                        .or_default()
                        .insert(fun.sig.name.node.clone(), scheme);

                    if old.is_some() {
                        panic!(
                            "{}: Associated function {} for type {} is defined multiple times",
                            loc_string(&item.loc),
                            fun.sig.name.node,
                            ty_con_id
                        );
                    }

                    tys.exit_scope();
                    assert_eq!(tys.len_scopes(), 2); // top-level, impl
                }
            }

            ast::TopDecl::Type(ty_decl) => {
                let rhs = match &ty_decl.node.rhs {
                    Some(rhs) => rhs,
                    None => {
                        tys.exit_scope();
                        continue;
                    }
                };

                for ty_var in &ty_decl.node.type_params {
                    tys.insert_var(ty_var.clone(), Ty::QVar(ty_var.clone()));
                }

                let ty_vars: Set<Id> = ty_decl.node.type_params.iter().cloned().collect();

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
                            let old = associated_schemes
                                .entry(ty_decl.node.name.clone())
                                .or_default()
                                .insert(con.name.clone(), scheme);
                            if old.is_some() {
                                panic!(
                                    "{}: Constructor {}.{} is defined multiple times",
                                    loc_string(&ty_decl.loc), // TODO: use con loc
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
                                loc_string(&ty_decl.loc), // TODO: use con loc
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

    (top_schemes, associated_schemes)
}

/// Type check a top-level function.
fn check_top_fun(fun: &ast::L<ast::FunDecl>, tys: &mut PgmTypes) {
    let mut var_gen = TyVarGen::default();
    let mut env: ScopeMap<Id, Ty> = ScopeMap::default();

    let scheme = tys.top_schemes.get(&fun.node.sig.name.node).unwrap();

    assert_eq!(tys.tys.len_scopes(), 1);
    tys.tys.enter_scope();

    for (var, _bounds) in &scheme.quantified_vars {
        tys.tys.insert_var(var.clone(), Ty::Con(var.clone()));
        tys.tys.insert_con(var.clone(), TyCon::opaque(var.clone()));
    }

    for (param_name, param_ty) in &fun.node.sig.params {
        env.insert(
            param_name.clone(),
            convert_ast_ty(&tys.tys, &param_ty.node, &fun.loc),
        );
    }

    let ret_ty = match &fun.node.sig.return_ty {
        Some(ty) => convert_ast_ty(&tys.tys, &ty.node, &ty.loc),
        None => Ty::Record(Default::default()),
    };

    let mut preds: PredSet = Default::default();

    if let Some(body) = &fun.node.body.as_ref() {
        check_stmts(
            &body.node,
            Some(&ret_ty),
            &ret_ty,
            0,
            &mut env,
            &mut var_gen,
            tys,
            &mut preds,
        );
    }

    tys.tys.exit_scope();

    // Converts vec to map.
    let quantified_vars: Map<Id, Map<Id, Map<Id, Ty>>> = scheme
        .quantified_vars
        .iter()
        .map(|(var, trait_map)| (var.clone(), trait_map.clone()))
        .collect();

    resolve_preds(&quantified_vars, tys, &preds);
}

/// Type check an `impl` block.
///
/// The block may be for a trait implementation or for associated functions.
///
/// `tys` is `mut` to be able to add type parameters of the `impl` and associated types before
/// checking the methods.
fn check_impl(impl_: &ast::L<ast::ImplDecl>, tys: &mut PgmTypes) {
    assert_eq!(tys.tys.len_scopes(), 1);
    tys.tys.enter_scope();

    // Bind trait type parameters.
    convert_and_bind_context(
        &mut tys.tys,
        &impl_.node.context,
        TyVarConversion::ToOpaque,
        &impl_.loc,
    );

    let trait_ty = convert_ast_ty(&tys.tys, &impl_.node.ty.node, &impl_.loc);
    let (ty_con_id, ty_args) = trait_ty.con(tys.tys.cons()).unwrap();

    // Bind associated types.
    bind_associated_types(impl_, &mut tys.tys);

    let ty_con = tys.tys.get_con(&ty_con_id).unwrap().clone();

    if let TyConDetails::Trait(TraitDetails {
        methods: trait_methods,
        ..
    }) = &ty_con.details
    {
        // Check that the method types match trait method types, with the trait type parameter
        // replaced by the implementing type.
        let mut ty_args = match ty_args {
            TyArgs::Positional(ty_args) => ty_args,
            TyArgs::Named(_) => panic!(),
        };

        assert_eq!(ty_args.len(), 1); // checked in the previous pass
        assert_eq!(ty_con.ty_params.len(), 1); // checked in the previous pass

        // Substitute `implementing_ty` for `trait_ty_param` in the trait method types.
        let implementing_ty = ty_args.pop().unwrap();
        let _trait_ty_param = &ty_con.ty_params[0].0;

        for item in &impl_.node.items {
            let fun = match &item.node {
                ast::ImplDeclItem::AssocTy(_) => continue,
                ast::ImplDeclItem::Fun(fun) => fun,
            };

            tys.tys.enter_scope();

            // Bind function type parameters.
            convert_and_bind_context(
                &mut tys.tys,
                &fun.sig.type_params,
                TyVarConversion::ToOpaque,
                &impl_.loc,
            );

            let fun_name: &Id = &fun.sig.name.node;

            let _trait_method = trait_methods.get(fun_name).unwrap_or_else(|| {
                panic!(
                    "{}: Trait {} does not have a method named {}",
                    loc_string(&item.loc),
                    ty_con_id,
                    fun_name
                )
            });

            // TODO: Type comparison below is not right:
            //
            // - We should either have QVars on both sides, or replace them with opaque types in
            //   the trait function type scheme.
            //
            // - We should allow using the RHS of associated types in the impl function. For
            //   example, this should be accepted:
            //
            //       trait T[A]:
            //           type X
            //           fn f(self): X
            //
            //       impl T[C]:
            //          type X = I32
            //          fn f(self): I32 = ...

            // Type of the method in the trait declaration, with `self` type substituted for the
            // type implementing the trait.
            /*
            let trait_fun_ty =
                trait_method
                    .scheme
                    .subst(trait_ty_param, &implementing_ty, &item.loc);

            // Type of the method in the impl declaration.
            let impl_fun_ty = convert_fun_ty(
                Some(&implementing_ty),
                &Default::default(),
                &fun.sig.type_params,
                &fun.sig.params,
                &fun.sig.return_ty,
                &item.loc,
                &tys.cons,
            );

            if !trait_fun_ty.eq_modulo_alpha(&Default::default(), &impl_fun_ty, &item.loc) {
                panic!(
                    "{}: Trait method implementation of {} does not match the trait method type
                    Trait method type:          {:?}
                    Implementation method type: {:?}",
                    loc_string(&item.loc),
                    fun_name,
                    trait_fun_ty,
                    impl_fun_ty
                );
            }
            */

            // Check the body.
            if let Some(body) = &fun.body {
                let ret_ty = match &fun.sig.return_ty {
                    Some(ty) => convert_ast_ty(&tys.tys, &ty.node, &ty.loc),
                    None => Ty::Record(Default::default()),
                };

                let mut preds: PredSet = Default::default();
                let mut env: ScopeMap<Id, Ty> = ScopeMap::default();
                let mut var_gen = TyVarGen::default();

                env.insert(SmolStr::new_static("self"), implementing_ty.clone());

                for (param_name, param_ty) in &fun.sig.params {
                    env.insert(
                        param_name.clone(),
                        convert_ast_ty(&tys.tys, &param_ty.node, &item.loc),
                    );
                }

                check_stmts(
                    &body.node,
                    Some(&ret_ty),
                    &ret_ty,
                    0,
                    &mut env,
                    &mut var_gen,
                    tys,
                    &mut preds,
                );

                // TODO: Context
                resolve_preds(&Default::default(), tys, &preds);
            }

            tys.tys.exit_scope();
        }
    } else {
        for item in &impl_.node.items {
            let fun = match &item.node {
                ast::ImplDeclItem::AssocTy(_) => continue,
                ast::ImplDeclItem::Fun(fun) => fun,
            };

            assert_eq!(tys.tys.len_scopes(), 2); // top-level, impl
            tys.tys.enter_scope();

            // Bind function type parameters.
            convert_and_bind_context(
                &mut tys.tys,
                &fun.sig.type_params,
                TyVarConversion::ToOpaque,
                &item.loc,
            );

            // Check the body.
            if let Some(body) = &fun.body {
                let ret_ty = match &fun.sig.return_ty {
                    Some(ty) => convert_ast_ty(&tys.tys, &ty.node, &ty.loc),
                    None => Ty::Record(Default::default()),
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

                check_stmts(
                    &body.node,
                    Some(&ret_ty),
                    &ret_ty,
                    0,
                    &mut env,
                    &mut var_gen,
                    tys,
                    &mut preds,
                );

                // TODO: Context
                resolve_preds(&Default::default(), tys, &preds);
            }

            tys.tys.exit_scope();
            assert_eq!(tys.tys.len_scopes(), 2); // top-level, impl
        }
    }

    tys.tys.exit_scope();
    assert_eq!(tys.tys.len_scopes(), 1);
}

/// We currently don't allow a type constructor to implement a trait multiple times with different
/// type arguments, e.g. `impl Debug[Vec[U32]]` and `impl Debug[Vec[Str]]` are not allowed at the
/// same time.
///
/// With this restriction resolving predicates is just a matter of checking for
/// `impl Trait[Con[T1, T2, ...]]` in the program, where `T1, T2, ...` are distrinct type variables.
// TODO: Add locations to error messages.
fn resolve_preds(_context: &Map<Id, Map<Id, Map<Id, Ty>>>, _tys: &PgmTypes, _preds: &PredSet) {
    /*
    for (var, traits) in preds {
        let var_ty = var.normalize();
        match var_ty {
            Ty::Con(con) | Ty::App(con, _) => {
                for trait_ in traits {
                    let TraitDetails {
                        implementing_tys, ..
                    } = tys.cons.get(trait_).unwrap().as_trait();

                    if !implementing_tys.contains(&con) {
                        panic!("Type {} does not implement trait {}", con, trait_);
                    }
                }
            }

            Ty::QVar(var) => {
                for trait_ in traits {
                    if context.get(&var).map(|context| context.contains(trait_)) != Some(true) {
                        panic!("Type variable {} does not implement trait {}", var, trait_);
                    }
                }
            }

            // TODO: Records can implement Debug, Eq, etc.
            Ty::Var(_)
            | Ty::Record(_)
            | Ty::Fun(_, _)
            | Ty::FunNamedArgs(_, _)
            | Ty::AssocTySelect { .. } => {
                if let Some(trait_) = traits.iter().next() {
                    panic!("Type {:?} does not implement trait {}", var_ty, trait_);
                }
            }
        }
    }
    */
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

fn loc_string(loc: &ast::Loc) -> String {
    format!(
        "{}:{}:{}",
        loc.module,
        loc.line_start + 1,
        loc.col_start + 1
    )
}
