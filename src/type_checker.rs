#![allow(clippy::mutable_key_type, clippy::for_kv_map)]

mod apply;
mod convert;
mod expr;
pub(crate) mod id;
pub(crate) mod kind_inference;
mod module_env;
mod normalization;
mod pat;
mod pat_coverage;
pub(crate) mod row_utils;
use crate::module_loader::LoadedPgm;
mod stmt;
mod traits;
mod ty;
mod ty_map;
mod unification;

pub use crate::utils::loc_display;
use convert::*;
pub use id::Id;
use normalization::normalize_stmt;
use stmt::check_stmts;
use traits::*;
use ty::*;
pub use ty::{FunArgs, Kind, RecordOrVariant, Ty};
use ty_map::TyMap;
use unification::unify;

use crate::ast::{self, Name};
use crate::collections::*;
use crate::module::ModulePath;

/// Maps names visible in a module to their `Id`s.
///
/// Names can be either unprefixed (from direct/selective imports) or prefixed (from
/// `import [Foo as P]`, accessed as `P/name`).
#[derive(Debug, Clone, Default)]
pub(super) struct ModuleEnv {
    /// Unprefixed names.
    pub names: HashMap<Name, Id>,

    /// Prefixed names: prefix -> name -> id.
    pub prefixed: HashMap<Name, HashMap<Name, Id>>,
}

impl ModuleEnv {
    /// Look up a name, optionally under a module prefix.
    fn get(&self, name: &Name, mod_prefix: Option<&Name>) -> Option<&Id> {
        match mod_prefix {
            None => self.names.get(name),
            Some(prefix) => self.prefixed.get(prefix)?.get(name),
        }
    }

    /// Look up a name with a module path prefix. Single-segment paths are treated as import
    /// prefixes (e.g. `P` in `import [Foo as P]`).
    fn get_with_path(
        &self,
        name: &Name,
        mod_prefix: &Option<crate::module::ModulePath>,
    ) -> Option<&Id> {
        match mod_prefix {
            None => self.names.get(name),
            Some(path) => {
                let segments = path.segments();
                assert_eq!(
                    segments.len(),
                    1,
                    "Multi-segment module paths not yet supported in name resolution"
                );
                self.prefixed.get(&Name::from(&segments[0]))?.get(name)
            }
        }
    }
}

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
    pub associated_fn_schemes: HashMap<Id, HashMap<Name, Scheme>>,

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
    pub method_schemes: HashMap<Name, Vec<(Id, Scheme)>>,

    /// Type constructor details.
    pub tys: TyMap,
}

/// Type check a module.
///
/// Updates trait implementation blocks with the default implementations of missing methods.
///
/// Returns schemes of top-level functions, associated functions (includes trait methods), and
/// details of type constructors (`TyCon`).
pub(crate) fn check_pgm(pgm: &mut LoadedPgm, main: &str) -> PgmTypes {
    add_exception_types(pgm, main);
    kind_inference::add_missing_type_params(pgm);
    let module_envs = module_env::generate_module_envs(pgm);
    let mut tys = collect_types(pgm, &module_envs);
    let trait_env = collect_trait_env(pgm, &mut tys.tys, &module_envs);
    for (module_path, decl) in pgm.iter_decls_mut() {
        let module_env = module_envs.get(module_path).unwrap();
        match &mut decl.node {
            ast::TopDecl::Import(_) => {}

            // Types and schemes added to `PgmTypes` by `collect_types`.
            ast::TopDecl::Type(_) | ast::TopDecl::Trait(_) => {}

            ast::TopDecl::Impl(impl_) => check_impl(impl_, &mut tys, &trait_env, module_env),

            ast::TopDecl::Fun(fun) => check_top_fun(fun, &mut tys, &trait_env, module_env),
        }
    }

    tys
}

pub(crate) fn check_main_type(
    tys: &PgmTypes,
    trait_env: &TraitEnv,
    main_module: &ModulePath,
    main: &str,
) {
    let main_id = Id::new(main_module, &Name::from(main));
    let main_scheme = tys
        .top_schemes
        .get(&main_id)
        .unwrap_or_else(|| panic!("Main function `{main}` is not defined."));

    if !main_scheme.quantified_vars.is_empty() || !main_scheme.preds.is_empty() {
        panic!("Main function `{main}` can't have quantified variables and predicates.");
    }

    unify(
        &main_scheme.ty,
        &Ty::Fun {
            args: FunArgs::Positional { args: vec![] },
            ret: Box::new(Ty::unit()),
            exceptions: Some(Box::new(Ty::empty_variant())),
        },
        tys.tys.cons(),
        trait_env,
        &UVarGen::default(),
        &main_scheme.loc,
        &[],
        &mut vec![],
    );
}

/// Add exception types to functions without one.
fn add_exception_types(pgm: &mut LoadedPgm, main: &str) {
    for (_, decl) in pgm.iter_decls_mut() {
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
                        ast::TraitDeclItem::Type { .. } => {}
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
    env: &'a mut ScopeMap<Name, Ty>,

    /// Whole program trait environment. Used to resolve closure predicate.s
    trait_env: &'a TraitEnv,

    /// Module environment for the current module.
    module_env: &'a ModuleEnv,

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

impl TcFunState<'_> {
    /// Resolve a `Name` from the AST to an `Id` using the current module's environment.
    fn resolve(&self, name: &Name) -> Id {
        resolve_name(self.module_env, name)
    }
}

/// Resolve a `Name` from the AST to an `Id` using a module environment. Only for module-level
/// definitions (types, traits, functions). Scoped names like associated type synonyms should be
/// looked up via `TyMap::resolve` instead.
pub(super) fn resolve_name(module_env: &ModuleEnv, name: &Name) -> Id {
    module_env
        .get(name, None)
        .cloned()
        .unwrap_or_else(|| panic!("Name `{}` not found in module environment", name))
}

const EXN_QVAR_ID: Name = Name::new_static("?exn");

/// Collect type constructors (traits and data) and type schemes (top-level, associated, traits) of
/// the program.
///
/// Does not type check the code, only collects types and type schemes.
fn collect_types(pgm: &mut LoadedPgm, module_envs: &HashMap<ModulePath, ModuleEnv>) -> PgmTypes {
    let mut tys = collect_cons(pgm, module_envs);
    add_default_impl_items(pgm, &mut tys, module_envs);
    let (top_schemes, associated_fn_schemes, method_schemes) =
        collect_schemes(pgm, &mut tys, module_envs);
    check_value_type_sizes(tys.cons());
    PgmTypes {
        top_schemes,
        associated_fn_schemes,
        method_schemes,
        tys,
    }
}

fn collect_cons(pgm: &mut LoadedPgm, module_envs: &HashMap<ModulePath, ModuleEnv>) -> TyMap {
    let mut tys: TyMap = Default::default();

    // Collect all type constructors first, then add fields and methods.
    for (module_path, decl) in pgm.iter_decls() {
        let module_env = module_envs
            .get(module_path)
            .unwrap_or_else(|| panic!("BUG: Module {module_path} is not in module envs"));
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
                let ty_id = resolve_name(module_env, &ty_decl.node.name);
                if tys.has_con(&ty_id) {
                    panic!(
                        "{}: Type {} is defined multiple times",
                        loc_display(&decl.loc),
                        ty_decl.node.name
                    );
                }
                tys.insert_con(
                    ty_id.clone(),
                    TyCon {
                        id: ty_id,
                        ty_params: ty_decl
                            .node
                            .type_params
                            .iter()
                            .map(|type_param| type_param.name.node.clone())
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
                let ty_id = resolve_name(module_env, &trait_decl.node.name.node);
                if tys.has_con(&ty_id) {
                    panic!(
                        "{}: Type {} is defined multiple times",
                        loc_display(&decl.loc),
                        trait_decl.node.name.node
                    );
                }

                tys.insert_con(
                    ty_id.clone(),
                    TyCon {
                        id: ty_id,
                        ty_params: trait_decl
                            .node
                            .type_params
                            .iter()
                            .map(|type_param| type_param.name.node.clone())
                            .zip(trait_decl.node.type_param_kinds.iter().cloned())
                            .collect(),
                        details: TyConDetails::Trait(TraitDetails {
                            methods: Default::default(),
                            assoc_tys: trait_decl
                                .node
                                .items
                                .iter()
                                .filter_map(|item| match item {
                                    ast::TraitDeclItem::Type {
                                        name,
                                        kind,
                                        default: _,
                                    } => Some((
                                        name.node.clone(),
                                        AssocTyDetails {
                                            kind: kind_inference::convert_kind(kind)
                                                .unwrap_or(Kind::Star),
                                            default: None, // we're not adding details in this pass
                                        },
                                    )),
                                    ast::TraitDeclItem::Fun(_) => None,
                                })
                                .collect(),
                        }),
                    },
                );
            }

            ast::TopDecl::Import(_) | ast::TopDecl::Fun(_) | ast::TopDecl::Impl(_) => {}
        }
    }

    // Convert and register type synonyms. This must happen after all type constructors are
    // registered (so synonym RHSs can reference them) and before fields/methods are processed (so
    // field types can reference synonyms).
    //
    // Synonyms can reference each other in any order, so we first collect all synonym definitions,
    // then resolve each one on demand with cycle detection.
    {
        let mut synonym_asts: HashMap<
            Name,
            (&ModulePath, &[ast::TypeParam], &[Kind], &ast::L<ast::Type>),
        > = Default::default();
        for (module_path, decl) in pgm.iter_decls() {
            if let ast::TopDecl::Type(ty_decl) = &decl.node
                && let Some(ast::TypeDeclRhs::Synonym(rhs_ty)) = &ty_decl.node.rhs
            {
                synonym_asts.insert(
                    ty_decl.node.name.clone(),
                    (
                        module_path,
                        &ty_decl.node.type_params,
                        &ty_decl.node.type_param_kinds,
                        rhs_ty,
                    ),
                );
            }
        }

        let mut resolving: HashSet<Name> = Default::default();
        let names: Vec<Name> = synonym_asts.keys().cloned().collect();
        for name in &names {
            resolve_synonym(name, &synonym_asts, &mut resolving, &mut tys, module_envs);
        }
    }

    // Add fields, methods, associated types.
    // This is where we start converting AST types to type checking types, so the ty con map should
    // be populated at this point.
    for (module_path, decl) in pgm.iter_decls() {
        let module_env = module_envs.get(module_path).unwrap();
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

                let ty_id = resolve_name(module_env, &ty_decl.node.name);
                tys.get_con_mut(&ty_id).unwrap().details = details;
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
                        .map(|type_param| type_param.name.node.clone())
                        .zip(trait_decl.node.type_param_kinds.iter().cloned())
                        .collect(),
                    preds: vec![],
                };

                let _trait_context: Vec<Pred> = convert_and_bind_context(
                    &mut tys,
                    module_env,
                    &trait_context_ast,
                    TyVarConversion::ToQVar,
                );

                let mut methods: HashMap<Name, TraitMethod> = HashMap::with_capacity_and_hasher(
                    trait_decl.node.items.len(),
                    Default::default(),
                );

                let mut assoc_tys: HashMap<Name, AssocTyDetails> = Default::default();

                for item in &trait_decl.node.items {
                    match item {
                        ast::TraitDeclItem::Type {
                            name: assoc_ty,
                            kind,
                            default,
                        } => {
                            let kind = kind_inference::convert_kind(kind).unwrap_or(Kind::Star);
                            let old = assoc_tys.insert(
                                assoc_ty.node.clone(),
                                AssocTyDetails {
                                    kind,
                                    default: default.clone(),
                                },
                            );
                            if old.is_some() {
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
                                    .map(|(type_param, kind)| {
                                        Ty::QVar(type_param.name.node.clone(), *kind)
                                    })
                                    .collect();
                                if args.is_empty() {
                                    Ty::Con(resolve_name(module_env, &trait_name), Kind::Star)
                                } else {
                                    Ty::App(resolve_name(module_env, &trait_name), args, Kind::Star)
                                }
                            };
                            tys.insert_synonym(
                                assoc_ty.node.clone(),
                                TyCon {
                                    id: Id::new(&ModulePath::new(vec![]), &assoc_ty.node),
                                    ty_params: vec![],
                                    details: TyConDetails::Synonym(Ty::AssocTySelect {
                                        ty: Box::new(trait_ty),
                                        assoc_ty: assoc_ty.node.clone(),
                                        kind,
                                    }),
                                },
                            );
                        }

                        ast::TraitDeclItem::Fun(fun) => {
                            // New scope for function context.
                            tys.enter_scope();

                            let fun_preds: Vec<Pred> = convert_and_bind_context(
                                &mut tys,
                                module_env,
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
                                    convert_ast_ty(&tys, module_env, &ty.node, &ty.loc)
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
                                    arg_tys.insert(
                                        0,
                                        convert_ast_ty(&tys, module_env, &ty.node, &ty.loc),
                                    );
                                }
                            }

                            let ret_ty: Ty = match &fun.node.sig.return_ty {
                                Some(ret_ty) => {
                                    convert_ast_ty(&tys, module_env, &ret_ty.node, &ret_ty.loc)
                                }
                                None => Ty::unit(),
                            };

                            let exceptions = match &fun.node.sig.exceptions {
                                Some(ty) => convert_ast_ty(&tys, module_env, &ty.node, &ty.loc),
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
                                    .map(|type_param| type_param.name.node.clone())
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

                let trait_id = resolve_name(module_env, &trait_decl.node.name.node);
                let ty_con = tys.get_con_mut(&trait_id).unwrap();
                ty_con.details = TyConDetails::Trait(TraitDetails { methods, assoc_tys });

                tys.exit_scope();
                assert_eq!(tys.len_scopes(), 1);
            }

            ast::TopDecl::Fun(_) | ast::TopDecl::Import(_) | ast::TopDecl::Impl(_) => continue,
        }
    }

    assert_eq!(tys.len_scopes(), 1);
    tys
}

// Add default methods to impls.
//
// We don't need to type check default methods copied to impls, but for now we do.
fn add_default_impl_items(
    pgm: &mut LoadedPgm,
    tys: &mut TyMap,
    module_envs: &HashMap<ModulePath, ModuleEnv>,
) {
    for (module_path, decl) in pgm.iter_decls_mut() {
        let module_env = module_envs.get(module_path).unwrap();
        let impl_decl = match &mut decl.node {
            ast::TopDecl::Impl(impl_decl) => &mut impl_decl.node,
            _ => continue,
        };

        let trait_con_id = resolve_name(module_env, &impl_decl.trait_.node);

        // Check that the trait in the impl block is really a trait.
        if !tys
            .get_con(&trait_con_id)
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
        let trait_arity = tys.get_con(&trait_con_id).unwrap().arity();
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
            convert_and_bind_context(tys, module_env, &impl_decl.context, TyVarConversion::ToQVar);

        let trait_ty_con = tys.get_con_mut(&trait_con_id).unwrap(); // checked above
        let trait_type_params = &trait_ty_con.ty_params;
        let (trait_methods, trait_assoc_tys) = match &mut trait_ty_con.details {
            TyConDetails::Trait(TraitDetails { methods, assoc_tys }) => (methods, assoc_tys),
            TyConDetails::Type { .. } | TyConDetails::Synonym(_) => {
                panic!() // checked above
            }
        };

        // Copy unimplemented associated types with defaults.
        for (assoc_ty_name, assoc_ty_details) in trait_assoc_tys {
            let assoc_ty_default = match &assoc_ty_details.default {
                Some(default) => default,
                None => {
                    // Type doesn't have a default, can't be copied.
                    continue;
                }
            };

            if impl_decl.items.iter().any(|item| match item {
                ast::ImplDeclItem::Type { assoc_ty, rhs: _ } => &assoc_ty.node == assoc_ty_name,
                ast::ImplDeclItem::Fun(_) => false,
            }) {
                // Impl implements the type, no need to copy.
                continue;
            }

            // Associated types can't have type parameters so there's no risk of shadowing impl's
            // type parameters.

            // Map type parameters of the trait to the impl types.
            let substs: HashMap<Name, ast::Type> = trait_type_params
                .iter()
                .map(|(param, _param_kind)| param.clone())
                .zip(impl_decl.tys.iter().map(|ty| ty.node.clone()))
                .collect();

            let default = assoc_ty_default.node.subst_ids(&substs);

            impl_decl.items.push(ast::ImplDeclItem::Type {
                assoc_ty: ast::L {
                    loc: ast::Loc::dummy(),
                    node: assoc_ty_name.clone(),
                },
                rhs: assoc_ty_default.map_as_ref(|_| default),
            });
        }

        // Copy unimplemented methods with defaults.
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
            let mut new_type_params: Vec<(Name, Kind)> =
                Vec::with_capacity(impl_fun_decl.node.sig.context.type_params.len());

            let renaming_substs: HashMap<Name, ast::Type> = impl_fun_decl
                .node
                .sig
                .context
                .type_params
                .iter()
                .map(|(ty_param, kind)| {
                    let new_param = Name::new(format!("{}$copy", ty_param));
                    new_type_params.push((new_param.clone(), *kind));
                    (ty_param.clone(), ast::Type::Var(new_param))
                })
                .collect();

            impl_fun_decl.node.sig.context.type_params = new_type_params;
            impl_fun_decl.node.sig.subst_ty_ids(&renaming_substs);

            // Map type parameters of the trait to the impl types.
            let substs: HashMap<Name, ast::Type> = trait_type_params
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
}

/// Resolve a type synonym by converting its RHS. If the RHS references another synonym, resolve
/// that one first (recursively). Detects cycles via the `resolving` set.
fn resolve_synonym(
    name: &Name,
    synonym_asts: &HashMap<Name, (&ModulePath, &[ast::TypeParam], &[Kind], &ast::L<ast::Type>)>,
    resolving: &mut HashSet<Name>,
    tys: &mut TyMap,
    module_envs: &HashMap<ModulePath, ModuleEnv>,
) {
    let (module_path, type_params, type_param_kinds, rhs_ty) = synonym_asts.get(name).unwrap();
    let module_env = module_envs.get(*module_path).unwrap();
    let syn_id = resolve_name(module_env, name);

    // Already resolved in a previous call.
    if tys.has_con(&syn_id) {
        return;
    }

    if !resolving.insert(name.clone()) {
        let cycle: Vec<&str> = resolving.iter().map(|id| id.as_str()).collect();
        panic!("Type synonym cycle detected: {}", cycle.join(", "));
    }

    // Resolve synonyms in the RHS.
    resolve_synonym_deps(&rhs_ty.node, synonym_asts, resolving, tys, module_envs);

    // Bind type params as QVars so they're available when converting the RHS.
    tys.enter_scope();
    for (param, kind) in type_params.iter().zip(type_param_kinds.iter()) {
        tys.insert_var(
            param.name.node.clone(),
            Ty::QVar(param.name.node.clone(), *kind),
        );
    }
    let converted = convert_ast_ty(tys, module_env, &rhs_ty.node, &rhs_ty.loc);
    tys.exit_scope();

    tys.insert_con(
        syn_id.clone(),
        TyCon {
            id: syn_id,
            ty_params: type_params
                .iter()
                .zip(type_param_kinds.iter())
                .map(|(p, k)| (p.name.node.clone(), *k))
                .collect(),
            details: TyConDetails::Synonym(converted),
        },
    );

    resolving.remove(name);
}

/// Recursively resolve any synonym dependencies in an AST type.
fn resolve_synonym_deps(
    ty: &ast::Type,
    synonym_asts: &HashMap<Name, (&ModulePath, &[ast::TypeParam], &[Kind], &ast::L<ast::Type>)>,
    resolving: &mut HashSet<Name>,
    tys: &mut TyMap,
    module_envs: &HashMap<ModulePath, ModuleEnv>,
) {
    match ty {
        ast::Type::Named(ast::NamedType {
            mod_prefix: _,
            name,
            args,
        }) => {
            if synonym_asts.contains_key(name) {
                resolve_synonym(name, synonym_asts, resolving, tys, module_envs);
            }
            for arg in args {
                resolve_synonym_deps(&arg.node, synonym_asts, resolving, tys, module_envs);
            }
        }
        ast::Type::Var(_) => {}
        ast::Type::Record { fields, .. } => {
            for (_, field_ty) in fields {
                resolve_synonym_deps(field_ty, synonym_asts, resolving, tys, module_envs);
            }
        }
        ast::Type::Variant { alts, .. } => {
            for alt in alts {
                for arg in &alt.args {
                    resolve_synonym_deps(&arg.node, synonym_asts, resolving, tys, module_envs);
                }
            }
        }
        ast::Type::Fn(ast::FnType {
            args,
            ret,
            exceptions,
        }) => {
            for arg in args {
                resolve_synonym_deps(&arg.node, synonym_asts, resolving, tys, module_envs);
            }
            if let Some(ret) = ret {
                resolve_synonym_deps(&ret.node, synonym_asts, resolving, tys, module_envs);
            }
            if let Some(exn) = exceptions {
                resolve_synonym_deps(&exn.node, synonym_asts, resolving, tys, module_envs);
            }
        }
        ast::Type::AssocTySelect { ty: inner, .. } => {
            resolve_synonym_deps(&inner.node, synonym_asts, resolving, tys, module_envs);
        }
    }
}

fn check_value_type_sizes(ty_cons: &ScopeMap<Id, TyCon>) {
    for ty_con in ty_cons.last().values() {
        let mut visited: HashSet<Id> = Default::default();
        let ty_args: Vec<Ty> = ty_con
            .ty_params
            .iter()
            .map(|(name, kind)| Ty::RVar(Name::new(format!("#{}", name)), *kind))
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
    ty_cons: &ScopeMap<Id, TyCon>,
    visited: &mut HashSet<Id>,
) -> bool {
    let ty_con_details = match &ty_con.details {
        TyConDetails::Trait(_) | TyConDetails::Synonym(_) => return false,
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

                Ty::Record { labels, .. } => {
                    for label_ty in labels.values() {
                        tys.push(label_ty);
                    }
                }

                Ty::Variant { labels, .. } => {
                    for label_ty in labels.values() {
                        tys.push(label_ty);
                    }
                }

                Ty::Fun { .. } | Ty::RVar(_, _) => {}

                Ty::QVar(_, _) | Ty::UVar(_) | Ty::AssocTySelect { .. } => {
                    panic!()
                }
            }
        }
    }

    visited.remove(&ty_con.id);
    false
}

// `tys` is `mut` to be able to update it with associated types when checking traits.
fn collect_schemes(
    pgm: &LoadedPgm,
    tys: &mut TyMap,
    module_envs: &HashMap<ModulePath, ModuleEnv>,
) -> (
    HashMap<Id, Scheme>,                // top schemes
    HashMap<Id, HashMap<Name, Scheme>>, // associated fn schemes
    HashMap<Name, Vec<(Id, Scheme)>>,   // method schemes (method name -> type id -> scheme)
) {
    let mut top_schemes: HashMap<Id, Scheme> = Default::default();
    let mut associated_fn_schemes: HashMap<Id, HashMap<Name, Scheme>> = Default::default();
    let mut method_schemes: HashMap<Name, Vec<(Id, Scheme)>> = Default::default();

    // Unique variable generator, used in substitutions to rename domain variables before
    // substitution to avoid capturing.
    // TODO: This should be generalized and used in all substitutions.
    let mut uniq_gen: u32 = 0;

    for (module_path, decl) in pgm.iter_decls() {
        let module_env = module_envs.get(module_path).unwrap();

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
                let trait_quantified_vars: Vec<(Name, Kind)> = trait_decl
                    .node
                    .type_params
                    .iter()
                    .map(|type_param| type_param.name.node.clone())
                    .zip(trait_decl.node.type_param_kinds.iter().cloned())
                    .collect();

                let trait_pred: ast::L<ast::Pred> = ast::L {
                    loc: trait_decl.loc.clone(),
                    node: ast::Pred::App(ast::NamedType {
                        mod_prefix: None,
                        name: trait_decl.node.name.node.clone(),
                        args: trait_decl
                            .node
                            .type_params
                            .iter()
                            .map(|type_param| {
                                type_param.name.map_as_ref(|type_param_name| {
                                    ast::Type::Var(type_param_name.clone())
                                })
                            })
                            .collect(),
                    }),
                };

                for item in &trait_decl.node.items {
                    let fun = match item {
                        ast::TraitDeclItem::Type { .. } => continue,
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
                    let fun_preds: Vec<Pred> = convert_and_bind_context(
                        tys,
                        module_env,
                        &context,
                        TyVarConversion::ToQVar,
                    );

                    // Add type synonyms for associated types so that e.g. `Item` resolves to
                    // `TraitName[params...].Item` within method signatures.
                    for trait_item in &trait_decl.node.items {
                        if let ast::TraitDeclItem::Type {
                            name: assoc_ty,
                            kind,
                            default: _,
                        } = trait_item
                        {
                            let kind = kind_inference::convert_kind(kind).unwrap_or(Kind::Star);
                            let trait_ty = {
                                let trait_name = trait_decl.node.name.node.clone();
                                let args: Vec<Ty> = trait_decl
                                    .node
                                    .type_params
                                    .iter()
                                    .zip(trait_decl.node.type_param_kinds.iter())
                                    .map(|(type_param, kind)| {
                                        Ty::QVar(type_param.name.node.clone(), *kind)
                                    })
                                    .collect();
                                if args.is_empty() {
                                    Ty::Con(resolve_name(module_env, &trait_name), Kind::Star)
                                } else {
                                    Ty::App(resolve_name(module_env, &trait_name), args, Kind::Star)
                                }
                            };
                            tys.insert_synonym(
                                assoc_ty.node.clone(),
                                TyCon {
                                    id: Id::new(&ModulePath::new(vec![]), &assoc_ty.node),
                                    ty_params: vec![],
                                    details: TyConDetails::Synonym(Ty::AssocTySelect {
                                        ty: Box::new(trait_ty),
                                        assoc_ty: assoc_ty.node.clone(),
                                        kind,
                                    }),
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
                            convert_ast_ty(tys, module_env, &ty.node, &ty.loc)
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
                            arg_tys.insert(0, convert_ast_ty(tys, module_env, &ty.node, &ty.loc));
                        }
                    }

                    let ret_ty: Ty = match &fun.node.sig.return_ty {
                        Some(ret_ty) => convert_ast_ty(tys, module_env, &ret_ty.node, &ret_ty.loc),
                        None => Ty::unit(),
                    };

                    let exceptions = match &fun.node.sig.exceptions {
                        Some(ty) => convert_ast_ty(tys, module_env, &ty.node, &ty.loc),
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
                            .push((
                                resolve_name(module_env, &trait_decl.node.name.node),
                                scheme.clone(),
                            ));
                    }

                    associated_fn_schemes
                        .entry(resolve_name(module_env, &trait_decl.node.name.node))
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
                    && module_env.get(&parent_ty.node, None).is_none()
                {
                    panic!(
                        "{}: Unknown type {}",
                        loc_display(&decl.loc),
                        &parent_ty.node
                    );
                }

                let fun_preds: Vec<Pred> = convert_and_bind_context(
                    tys,
                    module_env,
                    &sig.context,
                    TyVarConversion::ToQVar,
                );

                let mut arg_tys: Vec<Ty> = sig
                    .params
                    .iter()
                    .map(|(_name, ty)| {
                        let ty = ty.as_ref().unwrap();
                        convert_ast_ty(tys, module_env, &ty.node, &ty.loc)
                    })
                    .collect();

                match &sig.self_ {
                    ast::SelfParam::No => {}
                    ast::SelfParam::Implicit => {
                        // The parent type should have no type arguments.
                        match parent_ty {
                            Some(parent_ty) => {
                                // We checked above that the parent type exists.
                                let parent_ty_id = resolve_name(module_env, &parent_ty.node);
                                let parent_ty_con = tys.get_con(&parent_ty_id).unwrap();
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
                        arg_tys.insert(0, convert_ast_ty(tys, module_env, &ty.node, &ty.loc));
                    }
                }

                let ret_ty: Ty = match &sig.return_ty {
                    Some(ret_ty) => convert_ast_ty(tys, module_env, &ret_ty.node, &ret_ty.loc),
                    None => Ty::unit(),
                };

                let exceptions = match &sig.exceptions {
                    Some(ty) => convert_ast_ty(tys, module_env, &ty.node, &ty.loc),
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
                                method_schemes.entry(name.node.clone()).or_default().push((
                                    resolve_name(module_env, &parent_ty.node),
                                    scheme.clone(),
                                ));
                            }
                        }

                        let old = associated_fn_schemes
                            .entry(resolve_name(module_env, &parent_ty.node))
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
                        let id = resolve_name(module_env, &name.node);
                        let old = top_schemes.insert(id, scheme);
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
                for (type_param, kind) in ty_decl
                    .node
                    .type_params
                    .iter()
                    .zip(ty_decl.node.type_param_kinds.iter())
                {
                    tys.insert_var(
                        type_param.name.node.clone(),
                        Ty::QVar(type_param.name.node.clone(), *kind),
                    );
                }

                // Return type of constructors.
                let ret = if ty_decl.node.type_params.is_empty() {
                    Ty::Con(resolve_name(module_env, &ty_decl.node.name), Kind::Star)
                } else {
                    Ty::App(
                        resolve_name(module_env, &ty_decl.node.name),
                        ty_decl
                            .node
                            .type_params
                            .iter()
                            .zip(ty_decl.node.type_param_kinds.iter())
                            .map(|(type_param, kind)| Ty::QVar(type_param.name.node.clone(), *kind))
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
                            let ty = match convert_fields(tys, module_env, fields) {
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
                                    .map(|type_param| type_param.name.node.clone())
                                    .zip(ty_decl.node.type_param_kinds.iter().cloned())
                                    .collect(),
                                preds: Default::default(),
                                ty,
                                loc: ty_decl.loc.clone(), // TODO: use con loc
                            };
                            let old = tys
                                .get_con_mut(&resolve_name(module_env, &ty_decl.node.name))
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
                        let ty = match convert_fields(tys, module_env, fields) {
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
                                .map(|type_param| type_param.name.node.clone())
                                .zip(ty_decl.node.type_param_kinds.iter().cloned())
                                .collect(),
                            preds: Default::default(),
                            ty,
                            loc: ty_decl.loc.clone(), // TODO: use con loc
                        };
                        let old = tys
                            .get_con_mut(&resolve_name(module_env, &ty_decl.node.name))
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
                let _impl_assumps = convert_and_bind_context(
                    tys,
                    module_env,
                    &impl_decl.node.context,
                    TyVarConversion::ToQVar,
                );

                // Add type synonyms for associated types, mapping to
                // `TraitName[args...].AssocTyName` so that both trait and impl sides produce the
                // same `AssocTySelect` structure for `eq_modulo_alpha`.
                let trait_name = impl_decl.node.trait_.node.clone();
                let impl_trait_ty = {
                    let args: Vec<Ty> = impl_decl
                        .node
                        .tys
                        .iter()
                        .map(|ty| convert_ast_ty(tys, module_env, &ty.node, &ty.loc))
                        .collect();
                    if args.is_empty() {
                        Ty::Con(resolve_name(module_env, &trait_name), Kind::Star)
                    } else {
                        Ty::App(resolve_name(module_env, &trait_name), args, Kind::Star)
                    }
                };
                for item in &impl_decl.node.items {
                    if let ast::ImplDeclItem::Type { assoc_ty, .. } = item {
                        let trait_id = resolve_name(module_env, &trait_name);
                        let kind = tys
                            .get_con(&trait_id)
                            .unwrap()
                            .details
                            .trait_details()
                            .unwrap()
                            .assoc_tys
                            .get(&assoc_ty.node)
                            .unwrap_or_else(|| {
                                panic!(
                                    "{}: Trait {} does not have associated type {}",
                                    loc_display(&assoc_ty.loc),
                                    trait_name,
                                    assoc_ty.node,
                                )
                            })
                            .kind;
                        tys.insert_synonym(
                            assoc_ty.node.clone(),
                            TyCon {
                                id: Id::new(&ModulePath::new(vec![]), &assoc_ty.node),
                                ty_params: vec![],
                                details: TyConDetails::Synonym(Ty::AssocTySelect {
                                    ty: Box::new(impl_trait_ty.clone()),
                                    assoc_ty: assoc_ty.node.clone(),
                                    kind,
                                }),
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

                    let fun_assumps = convert_and_bind_context(
                        tys,
                        module_env,
                        &sig.context,
                        TyVarConversion::ToQVar,
                    );

                    let mut arg_tys: Vec<Ty> = sig
                        .params
                        .iter()
                        .map(|(_name, ty)| {
                            let ty = ty.as_ref().unwrap();
                            convert_ast_ty(tys, module_env, &ty.node, &ty.loc)
                        })
                        .collect();

                    match &sig.self_ {
                        ast::SelfParam::No => {}
                        ast::SelfParam::Implicit => panic!(
                            "{}: Impl method with implicit self type",
                            loc_display(&fun.loc)
                        ),
                        ast::SelfParam::Explicit(ty) => {
                            let ty = convert_ast_ty(tys, module_env, &ty.node, &ty.loc);
                            arg_tys.insert(0, ty);
                        }
                    }

                    let ret_ty: Ty = match &sig.return_ty {
                        Some(ret_ty) => convert_ast_ty(tys, module_env, &ret_ty.node, &ret_ty.loc),
                        None => Ty::unit(),
                    };

                    let exceptions = match &sig.exceptions {
                        Some(ty) => convert_ast_ty(tys, module_env, &ty.node, &ty.loc),
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

                    let impl_trait_id = resolve_name(module_env, &impl_decl.node.trait_.node);
                    let trait_ty_con = tys.get_con(&impl_trait_id).unwrap_or_else(|| {
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

                    let mut arg_fvs: OrderMap<Name, Option<Kind>> = Default::default();

                    for ((ty_param, _), ty_arg) in
                        trait_ty_con.ty_params.iter().zip(impl_decl.node.tys.iter())
                    {
                        let ty_param_renamed = rename_domain_var(ty_param, uniq);
                        kind_inference::collect_tvs(&ty_arg.node, &ty_arg.loc, &mut arg_fvs);
                        let ty_arg = convert_ast_ty(tys, module_env, &ty_arg.node, &ty_arg.loc);
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
fn check_top_fun(
    fun: &mut ast::L<ast::FunDecl>,
    tys: &mut PgmTypes,
    trait_env: &TraitEnv,
    module_env: &ModuleEnv,
) {
    let var_gen = UVarGen::default();
    let mut env: ScopeMap<Name, Ty> = ScopeMap::default();

    assert_eq!(tys.tys.len_scopes(), 1);
    tys.tys.enter_scope();

    // The predicates that we assume to hold in the function body.
    let assumps = convert_and_bind_context(
        &mut tys.tys,
        module_env,
        &fun.node.sig.context,
        TyVarConversion::ToRVar,
    );

    // TODO: This code is the same as collect_scheme's, maybe get arg and return types from the
    // scheme?
    match &fun.node.sig.self_ {
        ast::SelfParam::No => {}
        ast::SelfParam::Implicit => {
            // The parent type should have no type arguments.
            match &fun.node.parent_ty {
                Some(parent_ty) => {
                    let parent_ty_id = resolve_name(module_env, &parent_ty.node);
                    let parent_ty_con = tys.tys.get_con(&parent_ty_id).unwrap_or_else(|| {
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
                        Name::new_static("self"),
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
                Name::new_static("self"),
                convert_ast_ty(&tys.tys, module_env, &ty.node, &ty.loc),
            );
        }
    }

    for (param_name, param_ty) in &fun.node.sig.params {
        let param_ty = param_ty.as_ref().unwrap();
        env.insert(
            param_name.clone(),
            convert_ast_ty(&tys.tys, module_env, &param_ty.node, &fun.loc),
        );
    }

    let ret_ty = match &fun.node.sig.return_ty {
        Some(ty) => convert_ast_ty(&tys.tys, module_env, &ty.node, &ty.loc),
        None => Ty::unit(),
    };
    let mut preds: Vec<Pred> = Default::default();

    let exceptions = match &fun.node.sig.exceptions {
        Some(exc) => convert_ast_ty(&tys.tys, module_env, &exc.node, &exc.loc),
        None => panic!(),
    };

    let mut tc_state = TcFunState {
        return_ty: ret_ty.clone(),
        trait_env,
        module_env,
        env: &mut env,
        var_gen: &var_gen,
        tys,
        preds: &mut preds,
        exceptions,
        assumps: &assumps,
        local_gen: 0,
    };

    if let Some(body) = &mut fun.node.body.as_mut() {
        check_stmts(&mut tc_state, body, Some(&ret_ty), &mut Vec::new());
    }

    resolve_preds(trait_env, assumps, tys.tys.cons(), preds, &var_gen);

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
fn check_impl(
    impl_: &mut ast::L<ast::ImplDecl>,
    tys: &mut PgmTypes,
    trait_env: &TraitEnv,
    module_env: &ModuleEnv,
) {
    assert_eq!(tys.tys.len_scopes(), 1);
    tys.tys.enter_scope();

    let impl_assumps = convert_and_bind_context(
        &mut tys.tys,
        module_env,
        &impl_.node.context,
        TyVarConversion::ToRVar,
    );

    let trait_ty_con_id = &impl_.node.trait_;
    let trait_id = resolve_name(module_env, &trait_ty_con_id.node);

    let trait_ty_con = tys.tys.get_con(&trait_id).unwrap_or_else(|| {
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
            let assoc_ty_expected_kind = trait_details.assoc_tys.get(&assoc_ty.node).unwrap().kind;
            let converted = convert_ast_ty(&tys.tys, module_env, &rhs.node, &rhs.loc);
            if converted.kind() != assoc_ty_expected_kind {
                panic!(
                    "{}: Associated type {} is expected to have kind {}, but has kind {}",
                    loc_display(&assoc_ty.loc),
                    &assoc_ty.node,
                    assoc_ty_expected_kind,
                    converted.kind(),
                );
            }
            tys.tys.insert_synonym(
                assoc_ty.node.clone(),
                TyCon {
                    id: Id::new(&ModulePath::new(vec![]), &assoc_ty.node),
                    ty_params: vec![],
                    details: TyConDetails::Synonym(converted),
                },
            );
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
        let fun_assumps = convert_and_bind_context(
            &mut tys.tys,
            module_env,
            &fun.node.sig.context,
            TyVarConversion::ToRVar,
        );

        // Check the body.
        if let Some(body) = &mut fun.node.body {
            let ret_ty = match &fun.node.sig.return_ty {
                Some(ty) => convert_ast_ty(&tys.tys, module_env, &ty.node, &ty.loc),
                None => Ty::unit(),
            };

            let mut preds: Vec<Pred> = Default::default();
            let mut env: ScopeMap<Name, Ty> = ScopeMap::default();
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
                        Name::new("self"),
                        convert_ast_ty(&tys.tys, module_env, &ty.node, &ty.loc),
                    );
                }
            }

            for (param_name, param_ty) in &fun.node.sig.params {
                let param_ty = param_ty.as_ref().unwrap();
                env.insert(
                    param_name.clone(),
                    convert_ast_ty(&tys.tys, module_env, &param_ty.node, &param_ty.loc),
                );
            }

            let assumps = impl_assumps
                .iter()
                .cloned()
                .chain(fun_assumps.into_iter())
                .collect();

            let exceptions = match &fun.node.sig.exceptions {
                Some(exc) => convert_ast_ty(&tys.tys, module_env, &exc.node, &exc.loc),
                None => panic!(),
            };

            let mut tc_state = TcFunState {
                return_ty: ret_ty.clone(),
                trait_env,
                module_env,
                env: &mut env,
                var_gen: &var_gen,
                tys,
                preds: &mut preds,
                exceptions,
                assumps: &assumps,
                local_gen: 0,
            };

            check_stmts(&mut tc_state, body, Some(&ret_ty), &mut Vec::new());

            resolve_preds(trait_env, assumps, tys.tys.cons(), preds, &var_gen);

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
    let trait_method_ids: HashSet<&Name> = trait_details.methods.keys().collect();
    let mut implemented_method_ids: HashSet<&Name> = Default::default();
    let mut implemented_assoc_tys: HashSet<Name> = Default::default();
    for item in &impl_.node.items {
        let fun = match item {
            ast::ImplDeclItem::Type { assoc_ty, rhs: _ } => {
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
    let missing_methods: Vec<&&Name> = trait_method_ids
        .difference(&implemented_method_ids)
        .collect();
    if !missing_methods.is_empty() {
        panic!(
            "{}: Trait methods missing: {:?}",
            loc_display(&impl_.loc),
            missing_methods
        );
    }

    let missing_assoc_tys: Vec<&Name> = trait_details
        .assoc_tys
        .keys()
        .filter(|trait_assoc_ty| !implemented_assoc_tys.contains(*trait_assoc_ty))
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
    mut assumps: Vec<Pred>,
    cons: &ScopeMap<Id, TyCon>,
    mut goals: Vec<Pred>,
    var_gen: &UVarGen,
) {
    let mut progress = true;

    while progress {
        progress = false;
        let mut next_goals: Vec<Pred> = vec![];

        'goals: while let Some(mut pred) = goals.pop() {
            pred.params
                .iter_mut()
                .for_each(|ty| *ty = ty.deep_normalize(cons, trait_env, var_gen, &[]));

            if pred.trait_ == id::builtins::REC_ROW_TO_LIST() {
                resolve_row_to_list(trait_env, &pred, &mut next_goals, cons, var_gen);
                progress = true;
                continue;
            }

            for assump in assumps.iter_mut() {
                // Re-normalize assumption params so that `UVar`s linked by recent unifications
                // compare equal to the freshly-normalized goal params.
                assump
                    .params
                    .iter_mut()
                    .for_each(|ty| *ty = ty.deep_normalize(cons, trait_env, var_gen, &[]));

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
                            unify(
                                assump_rhs,
                                pred_rhs,
                                cons,
                                trait_env,
                                var_gen,
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
                        unify(
                            goal_assoc_ty_rhs,
                            matching_assoc_ty_rhs,
                            cons,
                            trait_env,
                            var_gen,
                            &pred.loc,
                            &[],
                            &mut next_goals,
                        );
                    }
                    // Add solved pred to assumptions to handle recursion.
                    assumps.push(pred);
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
}

/*
`RecRowToList[t]` always resolves for any `t`, but we need to check associated type selections to
rule out weird cases like `RecRowToList[t].List = U32`. E.g.

    foo[RecRowToList[r].List = U32](): ()
    main(): foo[row(msg: Str), []]()
*/
fn resolve_row_to_list(
    trait_env: &TraitEnv,
    pred: &Pred,
    next_goals: &mut Vec<Pred>,
    cons: &ScopeMap<Id, TyCon>,
    var_gen: &UVarGen,
) {
    assert_eq!(pred.params.len(), 1);
    let param = &pred.params[0];
    if let Ty::Record {
        labels,
        extension,
        is_row,
    } = param
        && let Some((assoc_ty_name, assoc_ty_rhs)) = &pred.assoc_ty
    {
        assert_eq!(assoc_ty_name, "List");
        assert!(is_row);
        // Note: we don't generate `RecRowToList[ext]` here (when `extension` is `Some(...)`). I'm
        // not sure if that's necessary as `RecRowToList[r]` will always resolve for any `r`.
        let list_ty = row_to_list_type(labels, extension);
        unify(
            &list_ty,
            assoc_ty_rhs,
            cons,
            trait_env,
            var_gen,
            &pred.loc,
            &[],
            next_goals,
        );
    }
}

fn row_to_list_type(labels: &OrdMap<Name, Ty>, extension: &Option<Box<Ty>>) -> Ty {
    let mut list_ty: Ty = match extension {
        None => Ty::empty_variant(),
        Some(ext) => Ty::AssocTySelect {
            ty: Box::new(Ty::App(
                id::builtins::REC_ROW_TO_LIST(),
                vec![*ext.clone()],
                Kind::Star,
            )),
            assoc_ty: Name::new_static("List"),
            kind: Kind::Star,
        },
    };

    for (_field_name, field_ty) in labels.iter().rev() {
        let record_field_ty = Ty::App(
            id::builtins::RECORD_FIELD(),
            vec![(*field_ty).clone()],
            Kind::Star,
        );
        list_ty = Ty::App(
            id::builtins::LIST(),
            vec![record_field_ty, list_ty],
            Kind::Star,
        );
    }

    list_ty
}

fn rename_domain_var(var: &Name, uniq: u32) -> Name {
    // Add the comment character '#' to make sure it won't conflict with a user variable.
    Name::new(format!("{var}#{uniq}"))
}

/// Expand type synonym references some of the `ast::Type` nodes in the module. This must run after
/// type checking and before monomorphization.
///
/// This only expands type synonyms in the `ast::Type`s in the AST that the monomorphiser uses. E.g.
/// it doesn't expand synonyms in `let` binding type annotations because monomorphiser doesn't use
/// those.
pub(crate) fn expand_type_synonyms(pgm: &mut LoadedPgm) {
    // Collect top-level synonyms with their type parameter names.
    let mut synonyms: HashMap<Name, (Vec<Name>, ast::Type)> = Default::default();
    for (_, decl) in pgm.iter_decls() {
        if let ast::TopDecl::Type(ty_decl) = &decl.node
            && let Some(ast::TypeDeclRhs::Synonym(rhs)) = &ty_decl.node.rhs
        {
            let params: Vec<Name> = ty_decl
                .node
                .type_params
                .iter()
                .map(|p| p.name.node.clone())
                .collect();
            synonyms.insert(ty_decl.node.name.clone(), (params, rhs.node.clone()));
        }
    }

    for (_, decl) in pgm.iter_decls_mut() {
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
                    if let ast::TraitDeclItem::Type {
                        name: assoc_ty,
                        kind: _,
                        default: _,
                    } = item
                    {
                        let trait_ty = ast::Type::Named(ast::NamedType {
                            mod_prefix: None,
                            name: trait_decl.node.name.node.clone(),
                            args: trait_decl
                                .node
                                .type_params
                                .iter()
                                .map(|type_param| {
                                    type_param.name.map_as_ref(|type_param_name| {
                                        ast::Type::Var(type_param_name.clone())
                                    })
                                })
                                .collect(),
                        });
                        scoped.insert(
                            assoc_ty.node.clone(),
                            (
                                vec![],
                                ast::Type::AssocTySelect {
                                    ty: assoc_ty.set_node(Box::new(trait_ty)),
                                    assoc_ty: assoc_ty.node.clone(),
                                },
                            ),
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
                        scoped.insert(assoc_ty.node.clone(), (vec![], rhs_expanded));
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

fn expand_synonyms_in_type_decl(
    decl: &mut ast::TypeDecl,
    synonyms: &HashMap<Name, (Vec<Name>, ast::Type)>,
) {
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

fn expand_synonyms_in_fields(
    fields: &mut ast::ConFields,
    synonyms: &HashMap<Name, (Vec<Name>, ast::Type)>,
) {
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

fn expand_synonyms_in_fun(
    fun: &mut ast::FunDecl,
    synonyms: &HashMap<Name, (Vec<Name>, ast::Type)>,
) {
    expand_synonyms_in_sig(&mut fun.sig, synonyms);
}

fn expand_synonyms_in_sig(sig: &mut ast::FunSig, synonyms: &HashMap<Name, (Vec<Name>, ast::Type)>) {
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

fn expand_synonyms_in_ty(ty: &mut ast::Type, synonyms: &HashMap<Name, (Vec<Name>, ast::Type)>) {
    match ty {
        ast::Type::Named(named) => {
            if let Some((params, body)) = synonyms.get(&named.name) {
                assert_eq!(
                    params.len(),
                    named.args.len(),
                    "Type synonym {} expects {} type arguments, found {}",
                    named.name,
                    params.len(),
                    named.args.len(),
                );
                let substs: HashMap<Name, &ast::Type> = params
                    .iter()
                    .zip(named.args.iter().map(|arg| &arg.node))
                    .map(|(param, arg)| (param.clone(), arg))
                    .collect();
                let mut expanded = body.clone();
                subst_ast_ty_vars(&mut expanded, &substs);
                *ty = expanded;
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

/// Same as `Ty::subst_qvars`, but for AST types. Used when expanding type synonyms in type
/// definitions.
fn subst_ast_ty_vars(ty: &mut ast::Type, vars: &HashMap<Name, &ast::Type>) {
    match ty {
        ast::Type::Var(v) => {
            if let Some(replacement) = vars.get(v) {
                *ty = (*replacement).clone();
            }
        }
        ast::Type::Named(named) => {
            for arg in &mut named.args {
                subst_ast_ty_vars(&mut arg.node, vars);
            }
        }
        ast::Type::Record {
            fields,
            extension,
            is_row: _,
        } => {
            for (_, field_ty) in fields {
                subst_ast_ty_vars(field_ty, vars);
            }
            if let Some(ext) = extension {
                subst_ast_ty_vars(&mut ext.node, vars);
            }
        }
        ast::Type::Variant {
            alts,
            extension,
            is_row: _,
        } => {
            for alt in alts {
                for arg in &mut alt.args {
                    subst_ast_ty_vars(&mut arg.node, vars);
                }
            }
            if let Some(ext) = extension {
                subst_ast_ty_vars(&mut ext.node, vars);
            }
        }
        ast::Type::Fn(fn_ty) => {
            for arg in &mut fn_ty.args {
                subst_ast_ty_vars(&mut arg.node, vars);
            }
            if let Some(ret) = &mut fn_ty.ret {
                subst_ast_ty_vars(&mut ret.node, vars);
            }
            if let Some(exn) = &mut fn_ty.exceptions {
                subst_ast_ty_vars(&mut exn.node, vars);
            }
        }
        ast::Type::AssocTySelect {
            ty: inner,
            assoc_ty: _,
        } => {
            subst_ast_ty_vars(&mut inner.node, vars);
        }
    }
}
