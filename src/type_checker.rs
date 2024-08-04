#![allow(clippy::too_many_arguments)]

use crate::ast;
use crate::collections::{Map, Set};
use crate::scope_map::ScopeMap;

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use smol_str::SmolStr;

// Syntax for type checking types.

// Use AST id type for now to avoid a renaming pass.
type Id = SmolStr;

/// A type scheme.
#[derive(Debug, Clone)]
struct Scheme {
    /// Generalized variables with predicates, e.g. `[T, [Eq]]` in the scheme for
    /// `fn id[T: Eq](a: T): T = a`.
    ///
    /// `Vec` instead of `Set` as type arguments in explicit type applications are ordered.
    ///
    /// For now, all quantified variables have kind `*`.
    quantified_vars: Vec<(Id, Vec<Id>)>,

    /// The generalized type.
    // TODO: Should we have separate fields for arguments types and return type?
    ty: Ty,

    /// Source code location of the variable with this type scheme. This is used in error messages
    /// and for debugging.
    loc: ast::Loc,
}

/// A type checking type.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Ty {
    /// A type constructor, e.g. `Vec`, `Option`, `U32`.
    Con(Id),

    /// A unification variable, created by a type scheme when instantiated.
    Var(TyVarRef),

    /// A type application, e.g. `Vec[U32]`, `Result[E, T]`.
    ///
    /// Because type variables have kind `*`, the constructor can only be a type constructor.
    ///
    /// Invariant: the vector is not empty.
    App(Id, Vec<Ty>),

    /// A record type, e.g. `(x: U32, y: U32)`.
    Record(Map<Id, Ty>),

    /// Only in type schemes: a quantified type variable.
    ///
    /// Instantiation converts these into unification variables (`Ty::Var`).
    QVar(Id),

    /// A function type, e.g. `Fn(U32): Str`.
    Fun(Vec<Ty>, Box<Ty>),

    /// A function type with named arguments, e.g. `Fn(x: U32, y: U32): Str`.
    FunNamedArgs(Map<Id, Ty>, Box<Ty>),
}

impl Ty {
    fn unit() -> Ty {
        Ty::Record(Default::default())
    }

    /// Substitute `ty` for `var` in `self`.
    fn subst(&self, var: &Id, ty: &Ty) -> Ty {
        todo!()
    }

    /// If the type is a unification variable, follow the links.
    ///
    /// Otherwise returns the original type.
    fn normalize(&self) -> Ty {
        match self {
            Ty::Var(var_ref) => {
                let link = match &*var_ref.0.link.borrow() {
                    Some(link) => link.normalize(),
                    None => return self.clone(),
                };
                var_ref.set_link(link.clone());
                link
            }
            other => other.clone(),
        }
    }

    /// Get the type constructor of the type and the type arguments.
    fn con(&self) -> Option<(Id, Vec<Ty>)> {
        match self {
            Ty::Con(con) => Some((con.clone(), vec![])),

            Ty::App(con, args) => Some((con.clone(), args.clone())),

            Ty::Var(_) | Ty::Record(_) | Ty::QVar(_) | Ty::Fun(_, _) | Ty::FunNamedArgs(_, _) => {
                None
            }
        }
    }

    /// Split a function type into the argument and return types.
    fn fun(&self) -> Option<(Vec<Ty>, Ty)> {
        match self {
            Ty::Fun(args, ret) => Some((args.clone(), (**ret).clone())),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct TyVarRef(Rc<TyVar>);

#[derive(Debug, Clone)]
struct TyVar {
    /// Identity of the unification variable.
    ///
    /// This is used to compare unification variables for equality.
    id: u32,

    /// Depth of the scope the unification variable was craeted in.
    level: Cell<u32>,

    /// When unified with a type, this holds the type.
    link: RefCell<Option<Ty>>,

    /// Source code location of the type scheme that generated this type variable. This is used in
    /// error messages and for debugging.
    loc: ast::Loc,
}

impl PartialEq for TyVar {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for TyVar {}

impl std::hash::Hash for TyVar {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state)
    }
}

impl TyVarRef {
    fn id(&self) -> u32 {
        self.0.id
    }

    fn level(&self) -> u32 {
        self.0.level.get()
    }

    fn link(&self) -> Option<Ty> {
        self.0.link.borrow().clone()
    }

    fn set_link(&self, ty: Ty) {
        *self.0.link.borrow_mut() = Some(ty);
    }

    fn prune_level(&self, level: u32) {
        let self_level = self.level();
        self.0.level.set(std::cmp::min(level, self_level));
    }
}

#[derive(Debug, Default)]
struct TyVarGen {
    next_id: u32,
}

impl TyVarGen {
    fn new_var(&mut self, level: u32, loc: ast::Loc) -> TyVarRef {
        let id = self.next_id;
        self.next_id += 1;
        TyVarRef(Rc::new(TyVar {
            id,
            level: Cell::new(level),
            link: RefCell::new(None),
            loc,
        }))
    }
}

/// A type constructor.
#[derive(Debug, Clone)]
struct TyCon {
    /// Name of the type.
    id: Id,

    /// Type parameters with bounds.
    ty_params: Vec<(Id, Vec<Ty>)>,

    /// Methods for traits, constructor for sums, fields for products.
    ///
    /// Types can refer to `ty_params`.
    details: TyConDetails,
}

/// A type constructor.
///
/// Types of methods and fields can refer to type parameters of the `TyCon`.
#[derive(Debug, Clone)]
enum TyConDetails {
    Trait { methods: Map<Id, Scheme> },
    Type { cons: Vec<ValCon> },
}

impl TyConDetails {
    fn placeholder() -> Self {
        TyConDetails::Type { cons: vec![] }
    }
}

/// A value constructor.
#[derive(Debug, Clone)]
struct ValCon {
    name: SmolStr,
    fields: ConFields,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ConFields {
    Unnamed(Vec<Ty>),
    Named(Map<SmolStr, Ty>),
}

impl TyCon {
    fn arity(&self) -> u32 {
        self.ty_params.len() as u32
    }

    fn is_trait(&self) -> bool {
        matches!(self.details, TyConDetails::Trait { .. })
    }
}

/// Type constructors and types in the program.
#[derive(Debug)]
struct PgmTypes {
    /// Type schemes of top-level values.
    top_schemes: Map<Id, Scheme>,

    /// Type schemes of associated functions.
    associated_schemes: Map<Id, Map<Id, Scheme>>,

    /// Type constructor details.
    cons: Map<Id, TyCon>,
}

fn collect_types(module: &ast::Module) -> PgmTypes {
    let cons = collect_cons(module);
    let (top_schemes, associated_schemes) = collect_schemes(module, &cons);
    PgmTypes {
        top_schemes,
        associated_schemes,
        cons,
    }
}

fn collect_cons(module: &ast::Module) -> Map<Id, TyCon> {
    let mut cons: Map<Id, TyCon> = Default::default();

    // Collect all type constructors first, then add bounds, fields, and methods.
    for decl in module {
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
    for decl in module {
        match &decl.node {
            ast::TopDecl::Type(ty_decl) => {
                let ty_con = cons.get(&ty_decl.node.name).unwrap();

                let details = match &ty_decl.node.rhs {
                    Some(rhs) => match rhs {
                        ast::TypeDeclRhs::Sum(sum_cons) => {
                            let cons: Vec<ValCon> = sum_cons
                                .iter()
                                .map(|ast::ConstructorDecl { name, fields }| ValCon {
                                    name: name.clone(),
                                    fields: convert_fields(&ty_con, fields, &cons, &decl.loc),
                                })
                                .collect();

                            TyConDetails::Type { cons }
                        }

                        ast::TypeDeclRhs::Product(fields) => TyConDetails::Type {
                            cons: vec![ValCon {
                                name: ty_decl.node.name.clone(),
                                fields: convert_fields(&ty_con, fields, &cons, &decl.loc),
                            }],
                        },
                    },

                    None => TyConDetails::Type { cons: vec![] },
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

                let trait_ty_params: Set<Id> =
                    [trait_decl.node.ty.node.0.clone()].into_iter().collect();

                let methods: Map<Id, Scheme> = trait_decl
                    .node
                    .funs
                    .iter()
                    .map(|sig| {
                        (
                            sig.node.name.node.clone(),
                            convert_fun_ty(
                                &trait_ty_params,
                                &sig.node.type_params,
                                &sig.node.params,
                                &sig.node.return_ty,
                                &sig.loc,
                                &cons,
                            ),
                        )
                    })
                    .collect();

                let con = cons.get_mut(&trait_decl.node.name.node).unwrap();
                assert_eq!(con.ty_params.len(), 1);

                con.ty_params[0].1 = bounds;
                con.details = TyConDetails::Trait { methods };
            }

            ast::TopDecl::Fun(_) | ast::TopDecl::Import(_) | ast::TopDecl::Impl(_) => continue,
        }
    }

    cons
}

fn convert_fields(
    ty_con: &TyCon,
    fields: &ast::ConstructorFields,
    ty_cons: &Map<Id, TyCon>,
    loc: &ast::Loc,
) -> ConFields {
    match fields {
        ast::ConstructorFields::Empty => ConFields::Unnamed(vec![]),
        ast::ConstructorFields::Named(named_fields) => ConFields::Named(
            named_fields
                .iter()
                .map(|(name, ty)| {
                    (
                        name.clone(),
                        convert_ast_ty(
                            &ty_cons,
                            &ty_con.ty_params.iter().map(|(id, _)| id.clone()).collect(),
                            ty,
                            loc,
                        ),
                    )
                })
                .collect(),
        ),
        ast::ConstructorFields::Unnamed(fields) => ConFields::Unnamed(
            fields
                .iter()
                .map(|ty| {
                    convert_ast_ty(
                        &ty_cons,
                        &ty_con.ty_params.iter().map(|(id, _)| id.clone()).collect(),
                        ty,
                        loc,
                    )
                })
                .collect(),
        ),
    }
}

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
                // Which type to add the method to.
                let ty_con: Id = match &impl_decl.node.ty.node {
                    ast::Type::Named(ast::NamedType { name, args }) => {
                        if ty_cons
                            .get(name)
                            .unwrap_or_else(|| {
                                panic!(
                                    "{}: Unknown type {}",
                                    loc_string(&impl_decl.node.ty.loc),
                                    name
                                )
                            })
                            .is_trait()
                        {
                            convert_ast_ty(
                                ty_cons,
                                &Default::default(),
                                &args[0].node,
                                &args[0].loc,
                            )
                            .con()
                            .unwrap()
                            .0
                        } else {
                            name.clone()
                        }
                    }
                    ast::Type::Record(_) => {
                        panic!("{}: Record type in impl block", loc_string(&impl_decl.loc))
                    }
                };

                let ty_ty_params: Set<Id> = impl_decl
                    .node
                    .context
                    .iter()
                    .map(|ty| ty.node.0.clone())
                    .collect();

                for fun in &impl_decl.node.funs {
                    let sig = &fun.node.sig;
                    let scheme = convert_fun_ty(
                        &ty_ty_params,
                        &sig.type_params,
                        &sig.params,
                        &sig.return_ty,
                        &fun.loc,
                        ty_cons,
                    );
                    let old = associated_schemes
                        .entry(ty_con.clone())
                        .or_default()
                        .insert(fun.node.sig.name.node.clone(), scheme);
                    if old.is_some() {
                        panic!(
                            "{}: Associated function {} for type {} is defined multiple times",
                            loc_string(&fun.loc),
                            fun.node.sig.name.node,
                            ty_con
                        );
                    }
                }
            }

            ast::TopDecl::Trait(_) | ast::TopDecl::Type(_) | ast::TopDecl::Import(_) => continue,
        }
    }

    (top_schemes, associated_schemes)
}

/// Convert a function type to a `Scheme`.
///
/// - `ty_ty_params`: When converting associated functions or trait methods, type parameters of the type.
/// - `fun_ty_params`: Type parameters of the function.
fn convert_fun_ty(
    ty_ty_params: &Set<Id>,
    fun_ty_params: &[ast::L<(ast::L<Id>, Vec<ast::L<Id>>)>],
    params: &[(SmolStr, ast::L<ast::Type>)],
    return_ty: &Option<ast::L<ast::Type>>,
    loc: &ast::Loc,
    ty_cons: &Map<Id, TyCon>,
) -> Scheme {
    let quantified_vars: Vec<(Id, Vec<Id>)> = fun_ty_params
        .iter()
        .map(
            |ast::L {
                 node: (ty, bounds),
                 loc: _,
             }| {
                (
                    ty.node.clone(),
                    bounds
                        .iter()
                        .map(|bound| {
                            if !ty_cons.contains_key(&bound.node) {
                                panic!();
                            }
                            bound.node.clone()
                        })
                        .collect(),
                )
            },
        )
        .collect();

    // Quantified variables of both the function and the type.
    let all_quantified_vars: Set<Id> = quantified_vars
        .iter()
        .map(|(param, _bounds)| param)
        .chain(ty_ty_params.iter())
        .cloned()
        .collect();

    let arg_tys: Vec<Ty> = params
        .iter()
        .map(|ty| convert_ast_ty(ty_cons, &all_quantified_vars, &ty.1.node, &ty.1.loc))
        .collect();

    let ret_ty = match return_ty {
        Some(ret_ty) => convert_ast_ty(ty_cons, &all_quantified_vars, &ret_ty.node, &ret_ty.loc),
        None => Ty::unit(),
    };

    let fun_ty = Ty::Fun(arg_tys, Box::new(ret_ty));

    Scheme {
        quantified_vars,
        ty: fun_ty,
        loc: loc.clone(),
    }
}

/// Convert an AST type to a type checking type.
fn convert_ast_ty(
    ty_cons: &Map<Id, TyCon>,
    quantified_tys: &Set<Id>,
    ast_ty: &ast::Type,
    loc: &ast::Loc,
) -> Ty {
    match ast_ty {
        ast::Type::Named(ast::NamedType { name, args }) => match ty_cons.get(name) {
            Some(con) => {
                if con.arity() as usize != args.len() {
                    panic!(
                        "{}: Incorrect number of type arguments, expected {}, found {}",
                        loc_string(loc),
                        con.arity(),
                        args.len()
                    )
                }

                let args: Vec<Ty> = args
                    .iter()
                    .map(|ty| convert_ast_ty(ty_cons, quantified_tys, &ty.node, &ty.loc))
                    .collect();

                if args.is_empty() {
                    Ty::Con(name.clone())
                } else {
                    Ty::App(name.clone(), args)
                }
            }
            None => {
                if quantified_tys.contains(name) {
                    Ty::QVar(name.clone())
                } else {
                    panic!("{}: Unknown type {}", loc_string(loc), name)
                }
            }
        },

        ast::Type::Record(fields) => Ty::Record(
            fields
                .iter()
                .map(|named_ty| {
                    (
                        named_ty.name.as_ref().unwrap().clone(),
                        convert_ast_ty(ty_cons, quantified_tys, &named_ty.node, loc),
                    )
                })
                .collect(),
        ),
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

impl Scheme {
    /// Instantiate the type scheme, return instantiated predicates and type.
    fn instantiate(&self, level: u32, var_gen: &mut TyVarGen) -> (Map<TyVarRef, Set<Id>>, Ty) {
        // TODO: We should rename type variables in a renaming pass, or disallow shadowing, or
        // handle shadowing here.

        let mut var_map: Map<Id, TyVarRef> = Default::default();
        let mut preds: Map<TyVarRef, Set<Id>> = Default::default();

        for (var, bounds) in &self.quantified_vars {
            let instantiated_var = var_gen.new_var(level, self.loc.clone());
            var_map.insert(var.clone(), instantiated_var.clone());
            preds.insert(instantiated_var.clone(), bounds.iter().cloned().collect());
        }

        (preds, self.ty.subst_qvars(&var_map))
    }
}

impl Ty {
    fn subst_qvars(&self, vars: &Map<Id, TyVarRef>) -> Ty {
        match self {
            Ty::Con(con) => Ty::Con(con.clone()),

            Ty::Var(var) => Ty::Var(var.clone()),

            Ty::App(ty, tys) => Ty::App(
                ty.clone(),
                tys.iter().map(|ty| ty.subst_qvars(vars)).collect(),
            ),

            Ty::Record(fields) => Ty::Record(
                fields
                    .iter()
                    .map(|(field_id, field_ty)| (field_id.clone(), field_ty.subst_qvars(vars)))
                    .collect(),
            ),

            Ty::QVar(id) => Ty::Var(vars.get(id).cloned().unwrap()),

            Ty::Fun(args, ret) => Ty::Fun(
                args.iter().map(|arg| arg.subst_qvars(vars)).collect(),
                Box::new(ret.subst_qvars(vars)),
            ),

            Ty::FunNamedArgs(args, ret) => Ty::FunNamedArgs(
                args.iter()
                    .map(|(name, ty)| (name.clone(), ty.subst_qvars(vars)))
                    .collect(),
                Box::new(ret.subst_qvars(vars)),
            ),
        }
    }
}

fn unify(ty1: &Ty, ty2: &Ty, loc: &ast::Loc) {
    match (ty1, ty2) {
        (Ty::Con(con1), Ty::Con(con2)) => {
            if con1 != con2 {
                panic!(
                    "Unable to unify types {} and {} at {}",
                    con1,
                    con2,
                    loc_string(loc)
                )
            }
        }

        (Ty::App(con1, args1), Ty::App(con2, args2)) => {
            if con1 != con2 {
                panic!(
                    "Unable to unify types {} and {} at {}",
                    con1,
                    con2,
                    loc_string(loc)
                )
            }

            // Kinds should've been checked.
            assert_eq!(args1.len(), args2.len());

            for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                unify(arg1, arg2, loc);
            }
        }

        (Ty::QVar(_), _) | (_, Ty::QVar(_)) => {
            panic!("QVar in unification at {}", loc_string(loc));
        }

        (Ty::Var(var1), Ty::Var(var2)) => {
            if var1.id() == var2.id() {
                return;
            }

            let var1_level = var1.level();
            let var2_level = var2.level();

            // We've normalized the types, so the links must be followed to the end.
            debug_assert!(var1.link().is_none());
            debug_assert!(var2.link().is_none());

            // Links must increase in level so that we can follow them to find the level of the
            // group.
            if var1_level < var2_level {
                link_var(var1, ty2);
            } else {
                link_var(var2, ty1);
            }
        }

        (Ty::Var(var), ty2) => link_var(var, ty2),

        (ty1, Ty::Var(var)) => link_var(var, ty1),

        (ty1, ty2) => panic!(
            "Unable to unify types {:?} and {:?} at {}",
            ty1,
            ty2,
            loc_string(loc)
        ),
    }
}

/// When we have an expected type during type inference (i.e. we're in 'checking' mode), this
/// unifies the expected type with the inferred type, and returns one of the types.
fn unify_expected_ty(ty: Ty, expected_ty: Option<&Ty>, loc: &ast::Loc) -> Ty {
    if let Some(expected_ty) = expected_ty {
        unify(&ty, expected_ty, loc);
    }
    ty
}

fn link_var(var: &TyVarRef, ty: &Ty) {
    // TODO: Occurs check.
    prune_level(ty, var.level());
    var.set_link(ty.clone());
}

fn prune_level(ty: &Ty, max_level: u32) {
    match ty {
        Ty::Con(_) => {}

        Ty::Var(var) => {
            assert!(var.link().is_none());
            var.prune_level(max_level);
        }

        Ty::App(_, tys) => {
            for ty in tys {
                prune_level(ty, max_level);
            }
        }

        Ty::Record(fields) => {
            for field_ty in fields.values() {
                prune_level(field_ty, max_level);
            }
        }

        Ty::QVar(_) => panic!("QVar in prune_level"),

        Ty::Fun(args, ret) => {
            for arg in args {
                prune_level(arg, max_level);
            }
            prune_level(ret, max_level);
        }

        Ty::FunNamedArgs(args, ret) => {
            for arg in args.values() {
                prune_level(arg, max_level);
            }
            prune_level(ret, max_level);
        }
    }
}

pub fn check_module(module: &ast::Module) {
    let tys = collect_types(module);

    for decl in module {
        match &decl.node {
            ast::TopDecl::Import(_) => panic!("Import declaration in check_module"),
            ast::TopDecl::Type(_) => {}
            ast::TopDecl::Trait(_) => todo!("Trait declaration in check_module"),
            ast::TopDecl::Impl(_) => todo!("Impl block in check_module"),
            ast::TopDecl::Fun(fun) => check_fun(fun, &tys),
        }
    }
}

fn check_fun(fun: &ast::L<ast::FunDecl>, tys: &PgmTypes) {
    let mut var_gen = TyVarGen::default();
    let mut env: ScopeMap<Id, Ty> = ScopeMap::default();

    // TODO: Add type parameters to the env.

    let mut quantified_vars: Set<Id> = Default::default();

    for (param_name, param_ty) in &fun.node.sig.params {
        env.bind(
            param_name.clone(),
            convert_ast_ty(&tys.cons, &quantified_vars, &param_ty.node, &fun.loc),
        );
    }

    let ret_ty = match &fun.node.sig.return_ty {
        Some(ty) => convert_ast_ty(&tys.cons, &quantified_vars, &ty.node, &ty.loc),
        None => Ty::Record(Default::default()),
    };

    let mut preds: Map<TyVarRef, Set<Id>> = Default::default();

    check_stmts(
        &fun.node.body.as_ref().unwrap().node,
        Some(&ret_ty),
        &ret_ty,
        0,
        &mut env,
        &mut var_gen,
        &quantified_vars,
        tys,
        &mut preds,
    );
}

fn check_stmts(
    stmts: &[ast::L<ast::Stmt>],
    expected_ty: Option<&Ty>,
    return_ty: &Ty,
    level: u32,
    env: &mut ScopeMap<Id, Ty>,
    var_gen: &mut TyVarGen,
    quantified_vars: &Set<Id>,
    tys: &PgmTypes,
    preds: &mut Map<TyVarRef, Set<Id>>,
) -> Ty {
    let num_stmts = stmts.len();
    assert!(num_stmts != 0);
    for (stmt_idx, stmt) in stmts.iter().enumerate() {
        let last = stmt_idx == num_stmts - 1;
        let stmt_ty = check_stmt(
            stmt,
            expected_ty,
            return_ty,
            level,
            env,
            var_gen,
            quantified_vars,
            tys,
            preds,
        );
        if last {
            if let Some(expected_ty) = expected_ty {
                unify(&stmt_ty, expected_ty, &stmt.loc);
            }
            return stmt_ty;
        }
    }
    panic!()
}

// TODO: Level is the same as the length of `env`, maybe remove the parameter?
fn check_stmt(
    stmt: &ast::L<ast::Stmt>,
    expected_ty: Option<&Ty>,
    return_ty: &Ty,
    level: u32,
    env: &mut ScopeMap<Id, Ty>,
    var_gen: &mut TyVarGen,
    quantified_vars: &Set<Id>,
    tys: &PgmTypes,
    preds: &mut Map<TyVarRef, Set<Id>>,
) -> Ty {
    match &stmt.node {
        ast::Stmt::Let(ast::LetStmt { lhs, ty, rhs }) => {
            // When type of the LHS is not given:
            //
            // (1) Infer the pattern type.
            // (2) Check the RHS using the inferred pattern type as the expected type.
            // (3) Bind the pattern variables.
            //
            // Otherwise start with (2), using the given type as the expected type.

            let pat_expected_ty = match ty {
                Some(ty) => convert_ast_ty(&tys.cons, quantified_vars, &ty.node, &ty.loc),
                None => infer_pat(lhs, level, var_gen, tys),
            };

            env.enter();
            let rhs_ty = check_expr(
                rhs,
                Some(&pat_expected_ty),
                return_ty,
                level + 1,
                env,
                var_gen,
                quantified_vars,
                tys,
                preds,
            );
            env.exit();

            unify(&rhs_ty, &pat_expected_ty, &rhs.loc);

            bind_pat(lhs, env);

            Ty::unit()
        }

        ast::Stmt::Assign(ast::AssignStmt { lhs, rhs, op }) => todo!(),

        ast::Stmt::Expr(expr) => check_expr(
            expr,
            expected_ty,
            return_ty,
            level,
            env,
            var_gen,
            quantified_vars,
            tys,
            preds,
        ),

        ast::Stmt::For(_) => todo!(),

        ast::Stmt::While(_) => todo!(),
    }
}

// TODO: When `expected_ty` is available should we unify with the expected type, or should the call
// site do it?
fn check_expr(
    expr: &ast::L<ast::Expr>,
    expected_ty: Option<&Ty>,
    return_ty: &Ty,
    level: u32,
    env: &mut ScopeMap<Id, Ty>,
    var_gen: &mut TyVarGen,
    quantified_vars: &Set<Id>,
    tys: &PgmTypes,
    preds: &mut Map<TyVarRef, Set<Id>>,
) -> Ty {
    match &expr.node {
        ast::Expr::Var(var) => {
            // Check if local.
            if let Some(ty) = env.get(var) {
                return unify_expected_ty(ty.clone(), expected_ty, &expr.loc);
            }

            if let Some(scheme) = tys.top_schemes.get(var) {
                let (scheme_preds, ty) = scheme.instantiate(level, var_gen);
                preds.extend(scheme_preds);
                return unify_expected_ty(ty, expected_ty, &expr.loc);
            }

            panic!("Unbound variable at {}", loc_string(&expr.loc));
        }

        ast::Expr::UpperVar(_) => todo!(),

        ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field }) => {
            let object_ty = check_expr(
                object,
                None,
                return_ty,
                level,
                env,
                var_gen,
                quantified_vars,
                tys,
                preds,
            );

            let ty = match object_ty {
                Ty::Con(con) => check_field_select(&con, &[], field, &expr.loc, tys),

                Ty::App(con, args) => check_field_select(&con, &args, field, &expr.loc, tys),

                Ty::Record(fields) => match fields.get(field) {
                    Some(field_ty) => field_ty.clone(),
                    None => panic!(
                        "{}: Record with fields {:?} does not have field {}",
                        loc_string(&object.loc),
                        fields.keys().collect::<Vec<_>>(),
                        field
                    ),
                },

                Ty::Var(_) | Ty::QVar(_) | Ty::Fun(_, _) | Ty::FunNamedArgs(_, _) => panic!(
                    "{}: Object in field selection does not have fields: {:?}",
                    loc_string(&object.loc),
                    object_ty
                ),
            };

            unify_expected_ty(ty, expected_ty, &expr.loc)
        }

        ast::Expr::ConstrSelect(_) => todo!(),

        ast::Expr::Call(ast::CallExpr { fun, args }) => {
            let fun_ty = check_expr(
                fun,
                None,
                return_ty,
                level,
                env,
                var_gen,
                quantified_vars,
                tys,
                preds,
            );

            match fun_ty {
                Ty::Fun(param_tys, ret_ty) => {
                    if param_tys.len() != args.len() {
                        panic!(
                            "{}: Function with arity {} is passed {} args",
                            loc_string(&expr.loc),
                            param_tys.len(),
                            args.len()
                        );
                    }

                    for arg in args {
                        if arg.name.is_some() {
                            panic!(
                                "{}: Named argument applied to function that expects positional arguments",
                                loc_string(&expr.loc),
                            );
                        }
                    }

                    let mut arg_tys: Vec<Ty> = Vec::with_capacity(args.len());
                    for (param_ty, arg) in param_tys.iter().zip(args.iter()) {
                        let arg_ty = check_expr(
                            &arg.expr,
                            Some(param_ty),
                            return_ty,
                            level,
                            env,
                            var_gen,
                            quantified_vars,
                            tys,
                            preds,
                        );
                        arg_tys.push(arg_ty);
                    }

                    for (param_ty, arg_ty) in param_tys.iter().zip(arg_tys.iter()) {
                        unify(param_ty, arg_ty, &expr.loc);
                    }

                    unify_expected_ty(*ret_ty, expected_ty, &expr.loc)
                }

                Ty::FunNamedArgs(param_tys, ret_ty) => {
                    if param_tys.len() != args.len() {
                        panic!(
                            "{}: Function with arity {} is passed {} args",
                            loc_string(&expr.loc),
                            param_tys.len(),
                            args.len()
                        );
                    }

                    for arg in args {
                        if arg.name.is_none() {
                            panic!(
                                "{}: Positional argument applied to function that expects named arguments",
                                loc_string(&expr.loc),
                            );
                        }
                    }

                    let param_names: Set<&SmolStr> = param_tys.keys().collect();
                    let arg_names: Set<&SmolStr> =
                        args.iter().map(|arg| arg.name.as_ref().unwrap()).collect();

                    if param_names != arg_names {
                        panic!(
                            "{}: Function expects arguments with names {:?}, but passed {:?}",
                            loc_string(&expr.loc),
                            param_names,
                            arg_names
                        );
                    }

                    for arg in args {
                        let arg_name: &SmolStr = arg.name.as_ref().unwrap();
                        let param_ty: &Ty = param_tys.get(arg_name).unwrap();
                        let arg_ty = check_expr(
                            &arg.expr,
                            Some(param_ty),
                            return_ty,
                            level,
                            env,
                            var_gen,
                            quantified_vars,
                            tys,
                            preds,
                        );
                        unify(&arg_ty, param_ty, &expr.loc);
                    }

                    unify_expected_ty(*ret_ty, expected_ty, &expr.loc)
                }

                _ => panic!(
                    "{}: Function in function application is not a function: {:?}",
                    loc_string(&expr.loc),
                    fun_ty,
                ),
            }
        }

        ast::Expr::Range(_) => todo!(),

        ast::Expr::Int(_) => {
            unify_expected_ty(Ty::Con(SmolStr::new_static("I32")), expected_ty, &expr.loc)
        }

        ast::Expr::String(_) => {
            unify_expected_ty(Ty::Con(SmolStr::new_static("Str")), expected_ty, &expr.loc)
        }

        ast::Expr::Char(_) => {
            unify_expected_ty(Ty::Con(SmolStr::new_static("Char")), expected_ty, &expr.loc)
        }

        ast::Expr::Self_ => todo!(),

        ast::Expr::BinOp(ast::BinOpExpr { left, right, op }) => {
            let method = match op {
                ast::BinOp::Add => "__add",
                ast::BinOp::Subtract => "__sub",
                ast::BinOp::Equal => "__eq",
                ast::BinOp::NotEqual => "__neq",
                ast::BinOp::Multiply => "__mul",
                ast::BinOp::Lt => "__lt",
                ast::BinOp::Gt => "__gt",
                ast::BinOp::LtEq => "__le",
                ast::BinOp::GtEq => "__ge",
                ast::BinOp::And => "__and",
                ast::BinOp::Or => "__or",
            };

            let desugared = ast::L {
                loc: expr.loc.clone(),
                node: ast::Expr::Call(ast::CallExpr {
                    fun: Box::new(ast::L {
                        loc: left.loc.clone(),
                        node: ast::Expr::FieldSelect(ast::FieldSelectExpr {
                            object: left.clone(),
                            field: SmolStr::new_static(method),
                        }),
                    }),
                    args: vec![
                        ast::CallArg {
                            name: None,
                            expr: (**left).clone(),
                        },
                        ast::CallArg {
                            name: None,
                            expr: (**right).clone(),
                        },
                    ],
                }),
            };

            check_expr(
                &desugared,
                expected_ty,
                return_ty,
                level,
                env,
                var_gen,
                quantified_vars,
                tys,
                preds,
            )
        }

        ast::Expr::UnOp(_) => todo!(),

        ast::Expr::ArrayIndex(_) => todo!(),

        ast::Expr::Record(_) => todo!(),

        ast::Expr::Return(_) => todo!(),

        ast::Expr::Match(_) => todo!(),

        ast::Expr::If(ast::IfExpr {
            branches,
            else_branch,
        }) => {
            let mut branch_tys: Vec<Ty> = Vec::with_capacity(branches.len() + 1);

            for (cond, body) in branches {
                let cond_ty = check_expr(
                    cond,
                    Some(&Ty::Con(SmolStr::new_static("Bool"))),
                    return_ty,
                    level,
                    env,
                    var_gen,
                    quantified_vars,
                    tys,
                    preds,
                );
                unify(&cond_ty, &Ty::Con(SmolStr::new_static("Bool")), &expr.loc);

                let body_ty = check_stmts(
                    body,
                    expected_ty,
                    return_ty,
                    level,
                    env,
                    var_gen,
                    quantified_vars,
                    tys,
                    preds,
                );

                branch_tys.push(body_ty);
            }

            match else_branch {
                Some(else_body) => {
                    let body_ty = check_stmts(
                        else_body,
                        expected_ty,
                        return_ty,
                        level,
                        env,
                        var_gen,
                        quantified_vars,
                        tys,
                        preds,
                    );
                    branch_tys.push(body_ty);
                }
                None => {
                    // A bit hacky: ensure that without an else branch the expression returns unit.
                    branch_tys.push(Ty::unit());
                }
            }

            // When expected type is available, unify with it for better errors.
            match expected_ty {
                Some(expected_ty) => {
                    for ty in &branch_tys {
                        unify(ty, expected_ty, &expr.loc);
                    }
                }
                None => {
                    for ty_pair in branch_tys.windows(2) {
                        unify(&ty_pair[0], &ty_pair[1], &expr.loc);
                    }
                }
            }

            branch_tys.pop().unwrap()
        }
    }
}

fn check_field_select(
    ty_con: &Id,
    ty_args: &[Ty],
    field: &Id,
    loc: &ast::Loc,
    tys: &PgmTypes,
) -> Ty {
    let ty_con = tys.cons.get(ty_con).unwrap();
    assert_eq!(ty_con.ty_params.len(), ty_args.len());

    match &ty_con.details {
        TyConDetails::Trait { methods: _ } => {
            // Stand-alone `trait.method` can't work, we need to look at the arguments.
            // Ignore this for now, we probably won't need it.
            todo!(
                "{}: FieldSelect expression selecting a trait method without receiver",
                loc_string(loc)
            );
        }

        TyConDetails::Type { cons } => match cons.len() {
            0 => panic!(
                "{}: BUG: Value with void type {}",
                loc_string(loc),
                ty_con.id,
            ),

            1 => {
                let con = &cons[0];
                match &con.fields {
                    ConFields::Unnamed(_) => panic!(
                        "{}: Type {} does not have named field {}",
                        loc_string(loc),
                        ty_con.id,
                        field
                    ),
                    ConFields::Named(fields) => match fields.get(field) {
                        Some(field_ty) => {
                            let mut field_ty = field_ty.clone();
                            for ((ty_param, _bounds), ty_arg) in
                                ty_con.ty_params.iter().zip(ty_args.iter())
                            {
                                field_ty = field_ty.subst(ty_param, ty_arg);
                            }
                            field_ty
                        }
                        None => panic!(
                            "{}: Type {} does not have field {}",
                            loc_string(loc),
                            ty_con.id,
                            field
                        ),
                    },
                }
            }

            _ => panic!(
                "{}: Cannot select field {} of sum type {}",
                loc_string(loc),
                field,
                ty_con.id,
            ),
        },
    }
}

fn infer_pat(pat: &ast::L<ast::Pat>, level: u32, var_gen: &mut TyVarGen, tys: &PgmTypes) -> Ty {
    match &pat.node {
        ast::Pat::Var(_) | ast::Pat::Ignore => Ty::Var(var_gen.new_var(level, pat.loc.clone())),

        ast::Pat::Constr(ast::ConstrPattern {
            constr: ast::Constructor { type_, constr },
            fields,
        }) => {
            let ty_con = tys
                .cons
                .get(type_)
                .unwrap_or_else(|| panic!("{}: Undefined type", loc_string(&pat.loc)));

            // TODO: Add constructors to `TyCon`, check that the `constr` is valid.
            // TODO: From patterns in `Constr` fields infer type parameters of the type.

            todo!()
        }

        ast::Pat::Record(fields) => Ty::Record(
            fields
                .iter()
                .map(|named| {
                    (
                        named.name.as_ref().unwrap().clone(),
                        infer_pat(&*named.node, level, var_gen, tys),
                    )
                })
                .collect(),
        ),

        ast::Pat::Str(_) | ast::Pat::StrPfx(_, _) => Ty::Con(SmolStr::new_static("Str")),

        ast::Pat::Char(_) => Ty::Con(SmolStr::new_static("Char")),

        ast::Pat::Or(pat1, pat2) => {
            let pat1_ty = infer_pat(pat1, level, var_gen, tys);
            let pat2_ty = infer_pat(pat2, level, var_gen, tys);
            // TODO: To check pattern bind the same variables of same types.
            // TODO: Any other checks here?
            unify(&pat1_ty, &pat2_ty, &pat.loc);
            pat1_ty
        }
    }
}

fn bind_pat(pat: &ast::L<ast::Pat>, env: &mut ScopeMap<Id, Ty>) {}
