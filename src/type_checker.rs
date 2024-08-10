#![allow(clippy::mutable_key_type)]

use crate::ast;
use crate::collections::{Map, Set};
use crate::interpolation::StringPart;
use crate::scope_map::ScopeMap;

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use smol_str::SmolStr;

// Syntax for type checking types.

// Use AST id type for now to avoid a renaming pass.
pub type Id = SmolStr;

/// A type scheme.
#[derive(Debug, Clone)]
pub struct Scheme {
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
pub enum Ty {
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

    /// Substitute `ty` for quantified `var` in `self`.
    fn subst(&self, var: &Id, ty: &Ty) -> Ty {
        match self {
            Ty::Con(id) => Ty::Con(id.clone()),

            Ty::Var(var) => Ty::Var(var.clone()),

            Ty::App(var, tys) => Ty::App(
                var.clone(),
                tys.iter().map(|arg_ty| arg_ty.subst(var, ty)).collect(),
            ),

            Ty::Record(fields) => Ty::Record(
                fields
                    .iter()
                    .map(|(field, field_ty)| (field.clone(), field_ty.subst(var, ty)))
                    .collect(),
            ),

            Ty::QVar(qvar) => {
                if qvar == var {
                    ty.clone()
                } else {
                    Ty::QVar(qvar.clone())
                }
            }

            Ty::Fun(args, ret) => Ty::Fun(
                args.iter().map(|arg_ty| arg_ty.subst(var, ty)).collect(),
                Box::new(ret.subst(var, ty)),
            ),

            Ty::FunNamedArgs(named_args, ret) => Ty::FunNamedArgs(
                named_args
                    .iter()
                    .map(|(name, arg_ty)| (name.clone(), arg_ty.subst(var, ty)))
                    .collect(),
                Box::new(ret.subst(var, ty)),
            ),
        }
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
    pub fn con(&self) -> Option<(Id, Vec<Ty>)> {
        match self.normalize() {
            Ty::Con(con) => Some((con.clone(), vec![])),

            Ty::App(con, args) => Some((con.clone(), args.clone())),

            Ty::Var(_) | Ty::Record(_) | Ty::QVar(_) | Ty::Fun(_, _) | Ty::FunNamedArgs(_, _) => {
                None
            }
        }
    }

    /// Split a function type into the argument and return types.
    fn fun(&self) -> Option<(Vec<Ty>, Ty)> {
        match self.normalize() {
            Ty::Fun(args, ret) => Some((args.clone(), (*ret).clone())),
            _ => None,
        }
    }

    fn is_void(&self) -> bool {
        match self {
            Ty::Con(con) => con == &SmolStr::new_static("Void"),
            _ => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TyVarRef(Rc<TyVar>);

#[derive(Debug, Clone)]
pub struct TyVar {
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
    // TODO: We should make this a field/method of `Ty` and give all types locations.
    #[allow(unused)]
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
pub struct TyCon {
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
    Type { cons: Vec<Id> },
}

impl TyConDetails {
    fn placeholder() -> Self {
        TyConDetails::Type { cons: vec![] }
    }
}

/// Types of fields of value constructors. Types may contain quantified types of the type.
// TODO: Why do we need this? Why not use the type scheme from the env?
#[derive(Debug, Clone, PartialEq, Eq)]
enum ConFields {
    Unnamed(Vec<Ty>),
    Named(Map<SmolStr, Ty>),
}

impl TyCon {
    fn arity(&self) -> u32 {
        self.ty_params.len() as u32
    }

    pub fn is_trait(&self) -> bool {
        matches!(self.details, TyConDetails::Trait { .. })
    }
}

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
                            let cons: Vec<Id> = sum_cons
                                .iter()
                                .map(|ast::ConstructorDecl { name, fields: _ }| name.clone())
                                .collect();

                            TyConDetails::Type { cons }
                        }

                        ast::TypeDeclRhs::Product(_fields) => TyConDetails::Type {
                            cons: vec![ty_decl.node.name.clone()],
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

                let self_ty_id = trait_decl.node.ty.node.0.clone();

                let trait_ty_params: Set<Id> = [self_ty_id.clone()].into_iter().collect();

                let self_ty = Ty::QVar(self_ty_id.clone());

                let methods: Map<Id, Scheme> = trait_decl
                    .node
                    .funs
                    .iter()
                    .map(|sig| {
                        (
                            sig.node.name.node.clone(),
                            convert_fun_ty(
                                if sig.node.self_ { Some(&self_ty) } else { None },
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
    ty_params: &Set<Id>,
    fields: &ast::ConstructorFields,
    ty_cons: &Map<Id, TyCon>,
    loc: &ast::Loc,
) -> Option<ConFields> {
    match fields {
        ast::ConstructorFields::Empty => None,
        ast::ConstructorFields::Named(named_fields) => Some(ConFields::Named(
            named_fields
                .iter()
                .map(|(name, ty)| (name.clone(), convert_ast_ty(ty_cons, ty_params, ty, loc)))
                .collect(),
        )),
        ast::ConstructorFields::Unnamed(fields) => Some(ConFields::Unnamed(
            fields
                .iter()
                .map(|ty| convert_ast_ty(ty_cons, ty_params, ty, loc))
                .collect(),
        )),
    }
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
                let mut ty_con = match ty_cons.get(&ty_con_id) {
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
                    let (ty_con_id_, ty_args_) = self_ty.con().unwrap_or_else(|| {
                        panic!(
                            "{}: Trait type argument needs to be a type constructor, but it is {:?}",
                            loc_string(&impl_decl.loc),
                            self_ty
                        )
                    });
                    ty_con_id = ty_con_id_;
                    ty_args = ty_args_;

                    ty_con = match ty_cons.get(&ty_con_id) {
                        Some(ty_con) => ty_con,
                        None => {
                            panic!("{}: Unknown type {}", loc_string(&impl_decl.loc), ty_con_id)
                        }
                    };

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

/// Convert a function type to a `Scheme`.
///
/// - `ty_ty_params`: When converting associated functions or trait methods, type parameters of the type.
/// - `fun_ty_params`: Type parameters of the function.
fn convert_fun_ty(
    self_ty: Option<&Ty>,
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

    let mut arg_tys: Vec<Ty> =
        Vec::with_capacity(params.len() + if self_ty.is_some() { 1 } else { 0 });

    if let Some(self_ty) = self_ty {
        arg_tys.push(self_ty.clone());
    }

    arg_tys.extend(
        params
            .iter()
            .map(|ty| convert_ast_ty(ty_cons, &all_quantified_vars, &ty.1.node, &ty.1.loc)),
    );

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
pub fn convert_ast_ty(
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

    fn instantiate_with_tys(&self, tys: &[Ty]) -> Ty {
        assert_eq!(tys.len(), self.quantified_vars.len());

        let mut ty = self.ty.clone();
        for ((quantified_var, bounds), ty_) in self.quantified_vars.iter().zip(tys.iter()) {
            assert!(bounds.is_empty());
            ty = ty.subst(quantified_var, ty_);
        }

        ty
    }

    /// Substitute `ty` for quantified `var` in `self`.
    fn subst(&self, var: &Id, ty: &Ty, _loc: &ast::Loc) -> Scheme {
        // TODO: This is a bit hacky.. In top-level functions `var` should be in `quantified_vars`,
        // but in associated functions and trait methods it can also be a type parameter of the
        // trait/type. For now we use the same subst method for both.
        Scheme {
            quantified_vars: self
                .quantified_vars
                .iter()
                .filter(|(var_, _bounds)| var_ != var)
                .cloned()
                .collect(),
            ty: self.ty.subst(var, ty),
            loc: self.loc.clone(),
        }
    }

    /// Compare two schemes for equality modulo alpha renaming of quantified types.
    fn eq_modulo_alpha(&self, other: &Scheme) -> bool {
        if self.quantified_vars.len() != other.quantified_vars.len() {
            return false;
        }

        // Map quantified variables to their indices.
        let left_vars: Map<Id, u32> = self
            .quantified_vars
            .iter()
            .enumerate()
            .map(|(i, (var, _bounds))| (var.clone(), i as u32))
            .collect();

        let right_vars: Map<Id, u32> = other
            .quantified_vars
            .iter()
            .enumerate()
            .map(|(i, (var, _bounds))| (var.clone(), i as u32))
            .collect();

        ty_eq_modulo_alpha(&self.ty, &other.ty, &left_vars, &right_vars)
    }
}

fn ty_eq_modulo_alpha(
    ty1: &Ty,
    ty2: &Ty,
    ty1_qvars: &Map<Id, u32>,
    ty2_qvars: &Map<Id, u32>,
) -> bool {
    match (ty1, ty2) {
        (Ty::Con(con1), Ty::Con(con2)) => con1 == con2,

        (Ty::Var(_), _) | (_, Ty::Var(_)) => panic!("Unification variable in ty_eq_modulo_alpha"),

        (Ty::App(con1, args1), Ty::App(con2, args2)) => {
            con1 == con2
                && args1.len() == args2.len()
                && args1
                    .iter()
                    .zip(args2.iter())
                    .all(|(ty1, ty2)| ty_eq_modulo_alpha(ty1, ty2, ty1_qvars, ty2_qvars))
        }

        (Ty::Record(fields1), Ty::Record(fields2)) => {
            let keys1: Set<&Id> = fields1.keys().collect();
            let keys2: Set<&Id> = fields2.keys().collect();

            if keys1 != keys2 {
                return false;
            }

            for key in keys1 {
                if !ty_eq_modulo_alpha(
                    fields1.get(key).unwrap(),
                    fields2.get(key).unwrap(),
                    ty1_qvars,
                    ty2_qvars,
                ) {
                    return false;
                }
            }

            true
        }

        (Ty::QVar(qvar1), Ty::QVar(qvar2)) => {
            let qvar1_idx = ty1_qvars.get(qvar1).unwrap();
            let qvar2_idx = ty2_qvars.get(qvar2).unwrap();
            qvar1_idx == qvar2_idx
        }

        (Ty::Fun(args1, ret1), Ty::Fun(args2, ret2)) => {
            if args1.len() != args2.len() {
                return false;
            }

            for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                if !ty_eq_modulo_alpha(arg1, arg2, ty1_qvars, ty2_qvars) {
                    return false;
                }
            }

            ty_eq_modulo_alpha(ret1, ret2, ty1_qvars, ty2_qvars)
        }

        (Ty::FunNamedArgs(args1, ret1), Ty::FunNamedArgs(args2, ret2)) => {
            let names1: Set<&Id> = args1.keys().collect();
            let names2: Set<&Id> = args2.keys().collect();

            if names1 != names2 {
                return false;
            }

            for name in names1 {
                let ty1 = args1.get(name).unwrap();
                let ty2 = args2.get(name).unwrap();
                if !ty_eq_modulo_alpha(ty1, ty2, ty1_qvars, ty2_qvars) {
                    return false;
                }
            }

            ty_eq_modulo_alpha(ret1, ret2, ty1_qvars, ty2_qvars)
        }

        _ => false,
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
    let ty1 = ty1.normalize();
    if ty1.is_void() {
        return;
    }

    let ty2 = ty2.normalize();
    if ty2.is_void() {
        return;
    }

    match (&ty1, &ty2) {
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
                link_var(var1, &ty2);
            } else {
                link_var(var2, &ty1);
            }
        }

        (Ty::Var(var), ty2) => link_var(var, ty2),

        (ty1, Ty::Var(var)) => link_var(var, ty1),

        (Ty::Record(fields1), Ty::Record(fields2)) => {
            let keys1: Set<&Id> = fields1.keys().collect();
            let keys2: Set<&Id> = fields2.keys().collect();

            let extras1: Set<&&Id> = keys1.difference(&keys2).collect();
            let extras2: Set<&&Id> = keys2.difference(&keys1).collect();

            if !extras1.is_empty() {
                panic!(
                    "{}: Unable to unify records: extra keys: {:?}",
                    loc_string(loc),
                    extras1
                );
            }

            if !extras2.is_empty() {
                panic!(
                    "{}: Unable to unify records: extra keys: {:?}",
                    loc_string(loc),
                    extras2
                );
            }

            if keys1 != keys2 {
                panic!(
                    "{}: Unable to unify records: keys don't match",
                    loc_string(loc)
                );
            }

            for key in keys1 {
                let ty1 = fields1.get(key).unwrap();
                let ty2 = fields2.get(key).unwrap();
                unify(ty1, ty2, loc);
            }
        }

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

pub fn check_module(module: &ast::Module) -> PgmTypes {
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

            ast::TopDecl::Fun(fun) => check_fun(fun, &tys),
        }
    }

    tys
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

    if let Some(body) = &fun.node.body.as_ref() {
        check_stmts(
            &body.node,
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
}

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

    if let TyConDetails::Trait {
        methods: trait_methods,
    } = &ty_con.details
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

            let trait_method_ty = trait_methods.get(fun_name).unwrap_or_else(|| {
                panic!(
                    "{}: Trait {} does not have a method named {}",
                    loc_string(&fun.loc),
                    ty_con_id,
                    fun_name
                )
            });

            let trait_method_ty = trait_method_ty.subst(trait_ty_param, &implementing_ty, &fun.loc);

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
            }
        }
    }
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
            let pat_expected_ty = ty.as_ref().map(|ast_ty| {
                convert_ast_ty(&tys.cons, quantified_vars, &ast_ty.node, &ast_ty.loc)
            });

            env.enter();
            let rhs_ty = check_expr(
                rhs,
                pat_expected_ty.as_ref(),
                return_ty,
                level + 1,
                env,
                var_gen,
                quantified_vars,
                tys,
                preds,
            );
            env.exit();

            let pat_ty = check_pat(lhs, level, env, var_gen, tys);

            unify(&pat_ty, &rhs_ty, &lhs.loc);

            Ty::unit()
        }

        ast::Stmt::Assign(ast::AssignStmt {
            lhs: _,
            rhs: _,
            op: _,
        }) => todo!(),

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
                extend_preds(preds, scheme_preds);
                return unify_expected_ty(ty, expected_ty, &expr.loc);
            }

            panic!("{}: Unbound variable {}", loc_string(&expr.loc), var);
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

            let ty = match object_ty.normalize() {
                Ty::Con(con) => {
                    check_field_select(&con, &[], field, &expr.loc, tys, level, var_gen, preds)
                }

                Ty::App(con, args) => {
                    check_field_select(&con, &args, field, &expr.loc, tys, level, var_gen, preds)
                }

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

        ast::Expr::ConstrSelect(ast::ConstrSelectExpr { ty, constr }) => {
            let scheme = tys
                .associated_schemes
                .get(ty)
                .unwrap_or_else(|| {
                    panic!(
                        "{}: Type {} is not in type environment",
                        loc_string(&expr.loc),
                        ty
                    )
                })
                .get(constr)
                .unwrap_or_else(|| {
                    panic!(
                        "{}: Type {} does not have the constructor {}",
                        loc_string(&expr.loc),
                        ty,
                        constr
                    )
                });
            let (con_preds, ty) = scheme.instantiate(level, var_gen);
            extend_preds(preds, con_preds);
            ty
        }

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

            // TODO: Handle passing self when `fun` is a `FieldSelect`.
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

        ast::Expr::String(parts) => {
            let str_ty = Ty::Con(SmolStr::new_static("Str"));

            for part in parts {
                match part {
                    StringPart::Str(_) => continue,
                    StringPart::Expr(expr) => {
                        check_expr(
                            expr,
                            Some(&str_ty),
                            return_ty,
                            level,
                            env,
                            var_gen,
                            quantified_vars,
                            tys,
                            preds,
                        );
                    }
                }
            }

            unify_expected_ty(Ty::Con(SmolStr::new_static("Str")), expected_ty, &expr.loc)
        }

        ast::Expr::Char(_) => {
            unify_expected_ty(Ty::Con(SmolStr::new_static("Char")), expected_ty, &expr.loc)
        }

        ast::Expr::Self_ => match env.get("self") {
            Some(self_ty) => unify_expected_ty(self_ty.clone(), expected_ty, &expr.loc),
            None => panic!("{}: Unbound self", loc_string(&expr.loc)),
        },

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
                    args: vec![ast::CallArg {
                        name: None,
                        expr: (**right).clone(),
                    }],
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

        ast::Expr::Match(ast::MatchExpr { scrutinee, alts }) => {
            let scrut_ty = check_expr(
                scrutinee,
                None,
                return_ty,
                level,
                env,
                var_gen,
                quantified_vars,
                tys,
                preds,
            );

            let mut rhs_tys: Vec<Ty> = Vec::with_capacity(alts.len());

            for ast::Alt {
                pattern,
                guard,
                rhs,
            } in alts
            {
                let pat_ty = check_pat(pattern, level, env, var_gen, tys);
                unify(&pat_ty, &scrut_ty, &pattern.loc);

                if let Some(guard) = guard {
                    check_expr(
                        guard,
                        Some(&Ty::Con(SmolStr::new_static("Bool"))),
                        return_ty,
                        level,
                        env,
                        var_gen,
                        quantified_vars,
                        tys,
                        preds,
                    );
                }

                rhs_tys.push(check_stmts(
                    rhs,
                    None,
                    return_ty,
                    level,
                    env,
                    var_gen,
                    quantified_vars,
                    tys,
                    preds,
                ));
            }

            for tys in rhs_tys.windows(2) {
                unify(&tys[0], &tys[1], &expr.loc);
            }

            rhs_tys.pop().unwrap()
        }

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
    level: u32,
    var_gen: &mut TyVarGen,
    preds: &mut Map<TyVarRef, Set<Id>>,
) -> Ty {
    match select_field(ty_con, ty_args, field, loc, tys) {
        Some(ty) => ty,
        None => match select_method(ty_con, ty_args, field, tys, loc) {
            Some(scheme) => {
                let (scheme_preds, ty) = scheme.instantiate(level, var_gen);
                extend_preds(preds, scheme_preds);

                // Type arguments of the receiver already substituted for type parameters in
                // `select_method`. Drop 'self' argument.
                match ty {
                    Ty::Fun(mut args, ret) => {
                        args.remove(0);
                        Ty::Fun(args, ret)
                    }
                    _ => panic!(
                        "{}: Type of method is not a function type: {:?}",
                        loc_string(loc),
                        ty
                    ),
                }
            }
            None => panic!(
                "{}: Type {} does not have field or method {}",
                loc_string(loc),
                ty_con,
                field
            ),
        },
    }
}

/// Try to select a field.
fn select_field(
    ty_con: &Id,
    ty_args: &[Ty],
    field: &Id,
    loc: &ast::Loc,
    tys: &PgmTypes,
) -> Option<Ty> {
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
            1 => {
                let con_name = &cons[0];
                let con_scheme = tys.top_schemes.get(con_name)?;
                let con_ty = con_scheme.instantiate_with_tys(ty_args);

                match con_ty {
                    Ty::FunNamedArgs(fields, _) => Some(fields.get(field)?.clone()),
                    _ => None,
                }
            }

            _ => None,
        },
    }
}

/// Try to select a method.
fn select_method(
    ty_con: &Id,
    ty_args: &[Ty],
    field: &Id,
    tys: &PgmTypes,
    loc: &ast::Loc,
) -> Option<Scheme> {
    let ty_con = tys.cons.get(ty_con).unwrap();
    assert_eq!(ty_con.ty_params.len(), ty_args.len());

    let ty_methods = tys.associated_schemes.get(&ty_con.id)?;
    let mut scheme = ty_methods.get(field)?.clone();

    for (ty_param, ty_arg) in ty_con.ty_params.iter().zip(ty_args.iter()) {
        scheme = scheme.subst(&ty_param.0, ty_arg, loc);
    }

    Some(scheme)
}

/// Infer type of the pattern, add variables bound by the pattern to `env`.
fn check_pat(
    pat: &ast::L<ast::Pat>,
    level: u32,
    env: &mut ScopeMap<Id, Ty>,
    var_gen: &mut TyVarGen,
    tys: &PgmTypes,
) -> Ty {
    match &pat.node {
        ast::Pat::Var(var) => {
            let ty = Ty::Var(var_gen.new_var(level, pat.loc.clone()));
            env.bind(var.clone(), ty.clone());
            ty
        }

        ast::Pat::Ignore => Ty::Var(var_gen.new_var(level, pat.loc.clone())),

        ast::Pat::Constr(ast::ConstrPattern {
            constr: ast::Constructor { type_, constr },
            fields: pat_fields,
        }) => {
            let ty_con: &TyCon = tys
                .cons
                .get(type_)
                .unwrap_or_else(|| panic!("{}: Undefined type", loc_string(&pat.loc)));

            let (con_scheme, con_str): (&Scheme, String) = {
                match &ty_con.details {
                    TyConDetails::Trait { .. } => panic!(
                        "{}: Type constructor {} is a trait",
                        loc_string(&pat.loc),
                        type_
                    ),

                    TyConDetails::Type { cons: _ } => match constr {
                        Some(constr) => (
                            tys.associated_schemes
                                .get(&ty_con.id)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "{}: BUG: Type {} doesn't have any schemes",
                                        loc_string(&pat.loc),
                                        ty_con.id
                                    )
                                })
                                .get(constr)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "{}: Type {} doesn't have a constructor named {}",
                                        loc_string(&pat.loc),
                                        &ty_con.id,
                                        constr
                                    )
                                }),
                            format!("{}.{}", ty_con.id, constr),
                        ),
                        None => (
                            tys.top_schemes.get(&ty_con.id).unwrap_or_else(|| {
                                panic!(
                                    "{}: BUG: type {} doesn't have a top-level scheme",
                                    loc_string(&pat.loc),
                                    &ty_con.id
                                )
                            }),
                            ty_con.id.to_string(),
                        ),
                    },
                }
            };

            let (con_preds, con_ty) = con_scheme.instantiate(level, var_gen);
            assert!(con_preds.is_empty());

            match con_ty {
                Ty::Con(_) => {
                    if pat_fields.is_empty() {
                        con_ty
                    } else {
                        panic!(
                            "{}: Constructor {} does not have any fields",
                            loc_string(&pat.loc),
                            con_str
                        )
                    }
                }

                Ty::Fun(args, ret) => {
                    if args.len() != pat_fields.len() {
                        panic!(
                            "{}: Constructor {} has {} fields, but pattern has {}",
                            loc_string(&pat.loc),
                            con_str,
                            args.len(),
                            pat_fields.len()
                        );
                    }

                    for (con_ty, field_pat) in args.iter().zip(pat_fields.iter()) {
                        if field_pat.name.is_some() {
                            panic!(
                                "{}: Constructor {} has no named fields",
                                loc_string(&pat.loc),
                                con_str
                            )
                        }
                        let field_pat_ty = check_pat(&field_pat.node, level, env, var_gen, tys);
                        unify(con_ty, &field_pat_ty, &pat.loc);
                    }

                    *ret
                }

                Ty::FunNamedArgs(args, ret) => {
                    if args.len() != pat_fields.len() {
                        panic!(
                            "{}: Constructor {} has {} fields, but pattern has {}",
                            loc_string(&pat.loc),
                            con_str,
                            args.len(),
                            pat_fields.len()
                        );
                    }

                    let mut seen: Set<&Id> = Default::default();
                    for pat_field in pat_fields {
                        match &pat_field.name {
                            Some(name) => {
                                if !seen.insert(name) {
                                    panic!("{}: Field with name {} occurs multiple times in the pattern", loc_string(&pat.loc), name);
                                }
                            }
                            None => {
                                panic!(
                                    "{}: Pattern for constructor {} has unnamed argument",
                                    loc_string(&pat.loc),
                                    con_str
                                );
                            }
                        }
                    }

                    let arg_keys: Set<&Id> = args.keys().collect();
                    if seen != arg_keys {
                        panic!("{}: Constructor {} has named fields {:?}, but pattern has named fields {:?}", loc_string(&pat.loc), con_str, arg_keys, seen);
                    }

                    for (arg_name, arg_ty) in &args {
                        let field_pat = pat_fields
                            .iter()
                            .find_map(|pat_field| {
                                if pat_field.name.as_ref().unwrap() == arg_name {
                                    Some(&pat_field.node)
                                } else {
                                    None
                                }
                            })
                            .unwrap();

                        let field_pat_ty = check_pat(field_pat, level, env, var_gen, tys);

                        unify(&field_pat_ty, arg_ty, &pat.loc);
                    }

                    *ret
                }

                other => panic!(
                    "{}: BUG: Weird constructor type: {:?}",
                    loc_string(&pat.loc),
                    other
                ),
            }
        }

        ast::Pat::Record(fields) => Ty::Record(
            fields
                .iter()
                .map(|named| {
                    (
                        named.name.as_ref().unwrap().clone(),
                        check_pat(&named.node, level, env, var_gen, tys),
                    )
                })
                .collect(),
        ),

        ast::Pat::Str(_) | ast::Pat::StrPfx(_, _) => Ty::Con(SmolStr::new_static("Str")),

        ast::Pat::Char(_) => Ty::Con(SmolStr::new_static("Char")),

        ast::Pat::Or(pat1, pat2) => {
            let pat1_ty = check_pat(pat1, level, env, var_gen, tys);
            let pat2_ty = check_pat(pat2, level, env, var_gen, tys);
            // TODO: Check that the patterns bind the same variables of same types.
            // TODO: Any other checks here?
            unify(&pat1_ty, &pat2_ty, &pat.loc);
            pat1_ty
        }
    }
}

fn extend_preds(preds: &mut Map<TyVarRef, Set<Id>>, new_preds: Map<TyVarRef, Set<Id>>) {
    for (ty_var, tys) in new_preds {
        preds.entry(ty_var).or_default().extend(tys);
    }
}
