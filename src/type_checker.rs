#![allow(clippy::mutable_key_type)]

mod convert;
mod expr;
mod pat;
mod stmt;
mod ty;
mod unification;

pub use convert::convert_ast_ty;
use convert::{convert_fields, convert_fun_ty};
use stmt::check_stmts;
pub use ty::Id;
use ty::*;

use crate::ast;
use crate::collections::{Map, Set};
use crate::scope_map::ScopeMap;

use smol_str::SmolStr;

/// Type constructors and types in the program.
#[derive(Debug)]
pub struct PgmTypes {
    /// Type schemes of top-level values.
    pub top_schemes: Map<Id, Scheme>,

    /// Type schemes of associated functions.
    pub associated_schemes: Map<Id, Map<Id, Scheme>>,

    /// Type constructor details.
    pub cons: Map<Id, TyCon>,
}

/// Type check a module.
///
/// Updates trait implementation blocks with the default implementations of missing methods.
///
/// Returns schemes of top-level functions, associated functions (includes trait methods), and
/// details of type constructors (`TyCon`).
pub fn check_module(module: &mut ast::Module) -> PgmTypes {
    let tys = collect_types(module);

    for decl in module {
        match &decl.node {
            ast::TopDecl::Import(_) => panic!(
                "{}: Import declaration in check_module",
                loc_string(&decl.loc)
            ),

            // Types and schemes added to `PgmTypes` by `collect_types`.
            ast::TopDecl::Type(_) | ast::TopDecl::Trait(_) => {}

            ast::TopDecl::Impl(impl_) => check_impl(impl_, &tys),

            ast::TopDecl::Fun(fun) => check_top_fun(fun, &tys),
        }
    }

    tys
}

/// Collect type constructors (traits and data) and type schemes (top-level, associated, traits) of
/// the program.
///
/// Does not type check the code, only collects types and type schemes.
fn collect_types(module: &mut ast::Module) -> PgmTypes {
    let cons = collect_cons(module);
    let (top_schemes, associated_schemes) = collect_schemes(module, &cons);
    PgmTypes {
        top_schemes,
        associated_schemes,
        cons,
    }
}

fn collect_cons(module: &mut ast::Module) -> Map<Id, TyCon> {
    let mut cons: Map<Id, TyCon> = Default::default();

    // Collect all type constructors first, then add bounds, fields, and methods.
    for decl in module.iter() {
        match &decl.node {
            ast::TopDecl::Type(ty_decl) => {
                let ty_name = ty_decl.node.name.clone();
                let ty_params = ty_decl.node.type_params.clone();
                let old = cons.insert(
                    ty_name.clone(),
                    TyCon {
                        id: ty_name.clone(),
                        ty_params: ty_params.into_iter().map(|ty| (ty, vec![])).collect(),
                        details: TyConDetails::placeholder(),
                    },
                );
                if old.is_some() {
                    panic!("Type {} is defined multiple times", ty_name);
                }
            }

            ast::TopDecl::Trait(trait_decl) => {
                let ty_name = trait_decl.node.name.node.clone();
                let ty_params = vec![trait_decl.node.ty.node.0.clone()];
                let old = cons.insert(
                    ty_name.clone(),
                    TyCon {
                        id: ty_name.clone(),
                        ty_params: ty_params.into_iter().map(|ty| (ty, vec![])).collect(),
                        details: TyConDetails::placeholder(),
                    },
                );
                if old.is_some() {
                    panic!("Type {} is defined multiple times", ty_name);
                }
            }

            ast::TopDecl::Import(_) | ast::TopDecl::Fun(_) | ast::TopDecl::Impl(_) => continue,
        }
    }

    // Add bounds, fields, methods.
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

                cons.get_mut(&ty_decl.node.name).unwrap().details = details;
            }

            ast::TopDecl::Trait(trait_decl) => {
                let bounds: Vec<Ty> = trait_decl
                    .node
                    .ty
                    .node
                    .1
                    .iter()
                    .map(|ty| convert_ast_ty(&cons, &Default::default(), &ty.node, &ty.loc))
                    .collect();

                let self_ty_id = trait_decl.node.ty.node.0.clone();

                let trait_ty_params: Set<Id> = [self_ty_id.clone()].into_iter().collect();

                let self_ty = Ty::QVar(self_ty_id.clone());

                let methods: Map<Id, TraitMethod> = trait_decl
                    .node
                    .funs
                    .iter()
                    .map(|fun| {
                        (fun.node.sig.name.node.clone(), {
                            let scheme = convert_fun_ty(
                                if fun.node.sig.self_ {
                                    Some(&self_ty)
                                } else {
                                    None
                                },
                                &trait_ty_params,
                                &fun.node.sig.type_params,
                                &fun.node.sig.params,
                                &fun.node.sig.return_ty,
                                &fun.loc,
                                &cons,
                            );
                            let fun_decl = fun.clone();
                            TraitMethod { scheme, fun_decl }
                        })
                    })
                    .collect();

                let con = cons.get_mut(&trait_decl.node.name.node).unwrap();
                assert_eq!(con.ty_params.len(), 1);

                con.ty_params[0].1 = bounds;
                con.details = TyConDetails::Trait(TraitDetails {
                    methods,
                    implementing_tys: Default::default(),
                });
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

        let quantified_tys: Set<Id> = impl_decl
            .context
            .iter()
            .map(|ty| ty.node.0.clone())
            .collect();

        let ty = convert_ast_ty(
            &cons,
            &quantified_tys,
            &impl_decl.ty.node,
            &impl_decl.ty.loc,
        );

        let (trait_con_id, args) = match ty.con() {
            Some(con_and_args) => con_and_args,
            None => continue,
        };

        let trait_ty_con = cons.get_mut(&trait_con_id).unwrap();

        let (trait_methods, trait_implementing_tys) = match &mut trait_ty_con.details {
            TyConDetails::Trait(TraitDetails {
                ref mut methods,
                ref mut implementing_tys,
            }) => (methods, implementing_tys),
            TyConDetails::Type { .. } => continue,
        };

        assert_eq!(args.len(), 1);
        assert_eq!(trait_ty_con.ty_params.len(), 1);

        // Type parameter of the trait, e.g. `T` in `trait Debug[T]: ...`.
        let trait_ty_param: Id = trait_ty_con.ty_params[0].0.clone();

        // Type constructor of the type implementing the trait.
        let (self_ty_con, _) = args[0].con().unwrap();

        if !trait_implementing_tys.insert(self_ty_con.clone()) {
            panic!(
                "{}: Trait {} is implemented for type {} multiple times",
                loc_string(&decl.loc),
                trait_con_id,
                self_ty_con
            );
        }

        let self_ast_ty = match &impl_decl.ty.node {
            ast::Type::Named(ast::NamedType { name: _, args }) => {
                assert_eq!(args.len(), 1);
                args[0].node.clone()
            }
            ast::Type::Record(_) | ast::Type::AssocType { .. } => panic!(), // can't happen
        };

        for (method, method_decl) in trait_methods {
            if impl_decl
                .funs
                .iter()
                .any(|fun| &fun.node.sig.name.node == method)
            {
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
                            param_ty.map(|ty| ty.subst_var(&trait_ty_param, &self_ast_ty)),
                        )
                    })
                    .collect();
                impl_decl.funs.push(fun_decl);
            }
        }
    }

    cons
}

// NB. For now top schemes include product constructors and associated schemes include sum
// constructors.
fn collect_schemes(
    module: &ast::Module,
    ty_cons: &Map<Id, TyCon>,
) -> (Map<Id, Scheme>, Map<Id, Map<Id, Scheme>>) {
    let mut top_schemes: Map<Id, Scheme> = Default::default();
    let mut associated_schemes: Map<Id, Map<Id, Scheme>> = Default::default();

    for decl in module {
        match &decl.node {
            ast::TopDecl::Fun(ast::L {
                node: ast::FunDecl { sig, body: _ },
                loc,
            }) => {
                let scheme = convert_fun_ty(
                    None,
                    &Default::default(),
                    &sig.type_params,
                    &sig.params,
                    &sig.return_ty,
                    loc,
                    ty_cons,
                );

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
                let ty_ty_params: Set<Id> = impl_decl
                    .node
                    .context
                    .iter()
                    .map(|ty| ty.node.0.clone())
                    .collect();

                let mut self_ty: Ty = convert_ast_ty(
                    ty_cons,
                    &ty_ty_params,
                    &impl_decl.node.ty.node,
                    &impl_decl.node.ty.loc,
                );

                let (mut ty_con_id, mut ty_args) = self_ty.con().unwrap();
                let ty_con = match ty_cons.get(&ty_con_id) {
                    Some(ty_con) => ty_con,
                    None => panic!("{}: Unknown type {}", loc_string(&impl_decl.loc), ty_con_id),
                };

                if ty_con.is_trait() {
                    if ty_args.len() != 1 {
                        panic!(
                            "{}: Trait {} should have one type argument",
                            loc_string(&impl_decl.loc),
                            ty_con_id
                        );
                    }

                    // Add the associated method to the type rather than to the trait.
                    self_ty = ty_args.pop().unwrap();
                    let (ty_con_id_, _) = self_ty.con().unwrap_or_else(|| {
                        panic!(
                            "{}: Trait type argument needs to be a type constructor, but it is {:?}",
                            loc_string(&impl_decl.loc),
                            self_ty
                        )
                    });
                    ty_con_id = ty_con_id_;

                    // TODO: Check that the method types match trait methods.
                }

                for fun in &impl_decl.node.funs {
                    let sig = &fun.node.sig;
                    let scheme = convert_fun_ty(
                        if sig.self_ { Some(&self_ty) } else { None },
                        &ty_ty_params,
                        &sig.type_params,
                        &sig.params,
                        &sig.return_ty,
                        &fun.loc,
                        ty_cons,
                    );
                    let old = associated_schemes
                        .entry(ty_con_id.clone())
                        .or_default()
                        .insert(fun.node.sig.name.node.clone(), scheme);
                    if old.is_some() {
                        panic!(
                            "{}: Associated function {} for type {} is defined multiple times",
                            loc_string(&fun.loc),
                            fun.node.sig.name.node,
                            ty_con_id
                        );
                    }
                }
            }

            ast::TopDecl::Type(ty_decl) => {
                let rhs = match &ty_decl.node.rhs {
                    Some(rhs) => rhs,
                    None => continue,
                };

                let ty_vars: Set<Id> = ty_decl.node.type_params.iter().cloned().collect();

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
                            let ty = match convert_fields(&ty_vars, fields, ty_cons, &ty_decl.loc) {
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
                                    .map(|ty_param| (ty_param.clone(), vec![]))
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
                        let ty = match convert_fields(&ty_vars, fields, ty_cons, &ty_decl.loc) {
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
                                .map(|ty_param| (ty_param.clone(), vec![]))
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

            ast::TopDecl::Trait(_) | ast::TopDecl::Import(_) => continue,
        }
    }

    (top_schemes, associated_schemes)
}

/// Type check a top-level function.
fn check_top_fun(fun: &ast::L<ast::FunDecl>, tys: &PgmTypes) {
    let mut var_gen = TyVarGen::default();
    let mut env: ScopeMap<Id, Ty> = ScopeMap::default();

    let quantified_vars: Map<Id, Set<Id>> = fun
        .node
        .sig
        .type_params
        .iter()
        .map(|param| {
            (
                param.node.0.node.clone(),
                param
                    .node
                    .1
                    .iter()
                    .map(|bound| bound.node.clone())
                    .collect(),
            )
        })
        .collect();

    let quantified_var_ids: Set<Id> = quantified_vars.keys().cloned().collect();

    for (param_name, param_ty) in &fun.node.sig.params {
        env.bind(
            param_name.clone(),
            convert_ast_ty(&tys.cons, &quantified_var_ids, &param_ty.node, &fun.loc),
        );
    }

    let ret_ty = match &fun.node.sig.return_ty {
        Some(ty) => convert_ast_ty(&tys.cons, &quantified_var_ids, &ty.node, &ty.loc),
        None => Ty::Record(Default::default()),
    };

    let mut preds: Map<TyVarRef, Set<Id>> = Default::default();

    if let Some(body) = &fun.node.body.as_ref() {
        check_stmts(
            &body.node,
            Some(&ret_ty),
            &ret_ty,
            0,
            &mut env,
            &mut var_gen,
            &quantified_var_ids,
            tys,
            &mut preds,
        );
    }

    resolve_preds(&quantified_vars, tys, &preds);
}

/// Type check an `impl` block.
///
/// The block may be for a trait implementation or for associated functions.
fn check_impl(impl_: &ast::L<ast::ImplDecl>, tys: &PgmTypes) {
    let quantified_tys: Set<Id> = impl_
        .node
        .context
        .iter()
        .map(|ty| ty.node.0.clone())
        .collect();

    let trait_ty = convert_ast_ty(&tys.cons, &quantified_tys, &impl_.node.ty.node, &impl_.loc);
    let (ty_con_id, mut ty_args) = trait_ty.con().unwrap();

    let ty_con = tys.cons.get(&ty_con_id).unwrap();

    if let TyConDetails::Trait(TraitDetails {
        methods: trait_methods,
        ..
    }) = &ty_con.details
    {
        // Check that the method types match trait method types, with the trait type parameter
        // replaced by the implementing type.
        assert_eq!(ty_args.len(), 1); // checked in the previous pass
        assert_eq!(ty_con.ty_params.len(), 1); // checked in the previous pass

        // Substitute `implementing_ty` for `trait_ty_param` in the trait method types.
        let implementing_ty = ty_args.pop().unwrap();
        let trait_ty_param = &ty_con.ty_params[0].0;

        for fun in &impl_.node.funs {
            let fun_name: &Id = &fun.node.sig.name.node;

            let trait_method = trait_methods.get(fun_name).unwrap_or_else(|| {
                panic!(
                    "{}: Trait {} does not have a method named {}",
                    loc_string(&fun.loc),
                    ty_con_id,
                    fun_name
                )
            });

            let trait_method_ty =
                trait_method
                    .scheme
                    .subst(trait_ty_param, &implementing_ty, &fun.loc);

            let fun_ty = convert_fun_ty(
                Some(&implementing_ty),
                &quantified_tys,
                &fun.node.sig.type_params,
                &fun.node.sig.params,
                &fun.node.sig.return_ty,
                &fun.loc,
                &tys.cons,
            );

            if !trait_method_ty.eq_modulo_alpha(&fun_ty) {
                panic!(
                    "{}: Trait method implementation of {} does not match the trait method type
                    Trait method type:          {:?}
                    Implementation method type: {:?}",
                    loc_string(&fun.loc),
                    fun_name,
                    trait_method_ty,
                    fun_ty
                );
            }

            // Check the body.
            if let Some(body) = &fun.node.body {
                let ret_ty = match &fun.node.sig.return_ty {
                    Some(ty) => convert_ast_ty(&tys.cons, &quantified_tys, &ty.node, &ty.loc),
                    None => Ty::Record(Default::default()),
                };

                let mut preds: Map<TyVarRef, Set<Id>> = Default::default();
                let mut env: ScopeMap<Id, Ty> = ScopeMap::default();
                let mut var_gen = TyVarGen::default();

                env.bind(SmolStr::new_static("self"), implementing_ty.clone());

                for (param_name, param_ty) in &fun.node.sig.params {
                    env.bind(
                        param_name.clone(),
                        convert_ast_ty(&tys.cons, &quantified_tys, &param_ty.node, &fun.loc),
                    );
                }

                check_stmts(
                    &body.node,
                    Some(&ret_ty),
                    &ret_ty,
                    0,
                    &mut env,
                    &mut var_gen,
                    &quantified_tys,
                    tys,
                    &mut preds,
                );

                // TODO: Context
                resolve_preds(&Default::default(), tys, &preds);
            }
        }
    } else {
        for fun in &impl_.node.funs {
            // Check the body.
            if let Some(body) = &fun.node.body {
                let ret_ty = match &fun.node.sig.return_ty {
                    Some(ty) => convert_ast_ty(&tys.cons, &quantified_tys, &ty.node, &ty.loc),
                    None => Ty::Record(Default::default()),
                };

                let mut preds: Map<TyVarRef, Set<Id>> = Default::default();
                let mut env: ScopeMap<Id, Ty> = ScopeMap::default();
                let mut var_gen = TyVarGen::default();

                env.bind(SmolStr::new_static("self"), trait_ty.clone());

                for (param_name, param_ty) in &fun.node.sig.params {
                    env.bind(
                        param_name.clone(),
                        convert_ast_ty(&tys.cons, &quantified_tys, &param_ty.node, &fun.loc),
                    );
                }

                check_stmts(
                    &body.node,
                    Some(&ret_ty),
                    &ret_ty,
                    0,
                    &mut env,
                    &mut var_gen,
                    &quantified_tys,
                    tys,
                    &mut preds,
                );

                // TODO: Context
                resolve_preds(&Default::default(), tys, &preds);
            }
        }
    }
}

/// We currently don't allow a type constructor to implement a trait multiple times with different
/// type arguments, e.g. `impl Debug[Vec[U32]]` and `impl Debug[Vec[Str]]` are not allowed at the
/// same time.
///
/// With this restriction resolving predicates is just a matter of checking for
/// `impl Trait[Con[T1, T2, ...]]` in the program, where `T1, T2, ...` are distrinct type variables.
// TODO: Add locations to error messages.
fn resolve_preds(context: &Map<Id, Set<Id>>, tys: &PgmTypes, preds: &Map<TyVarRef, Set<Id>>) {
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
}

fn loc_string(loc: &ast::Loc) -> String {
    format!(
        "{}:{}:{}",
        loc.module,
        loc.line_start + 1,
        loc.col_start + 1
    )
}
