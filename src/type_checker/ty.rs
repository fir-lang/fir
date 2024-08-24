//! Syntax for type checking types.

use crate::ast;
use crate::collections::{Map, Set};
use crate::type_checker::loc_string;

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use smol_str::SmolStr;

// Use AST id type for now to avoid a renaming pass.
pub type Id = SmolStr;

/// A type scheme.
#[derive(Debug, Clone)]
pub struct Scheme {
    /// Generalized variables with predicates.
    ///
    /// `Vec` instead of `Map` as type arguments in explicit type applications are ordered. A type
    /// variable cannot appear multiple times in the `Vec`.
    ///
    /// For now, all quantified variables have kind `*`.
    ///
    /// The bounds can refer to the associated types, e.g. `[A, I: Iterator[Item = A]]`.
    ///
    /// In the example `[A, I: Iterator[Item = A]]`, this field will be:
    ///
    /// ```ignore
    /// [
    ///     (A, {}),
    ///     (I, {Iterator => {Item => A}})
    /// ]
    /// ```
    pub(super) quantified_vars: Vec<(Id, Map<Id, Map<Id, Ty>>)>,

    /// The generalized type.
    // TODO: Should we have separate fields for arguments types and return type?
    pub(super) ty: Ty,

    /// Source code location of the variable with this type scheme. This is used in error messages
    /// and for debugging.
    pub(super) loc: ast::Loc,
}

/// A type checking type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
    /// A type constructor, e.g. `Vec`, `Option`, `U32`.
    Con(Id),

    /// A unification variable, created by a type scheme when instantiated.
    Var(TyVarRef),

    /// A type application, e.g. `Vec[U32]`, `Result[E, T]`, `Iterator[Item = A]`.
    ///
    /// Because type variables have kind `*`, the constructor can only be a type constructor.
    ///
    /// Invariant: the vector is not empty.
    App(Id, TyArgs),

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

    /// Select an associated type of a type, e.g. in `T.Item` `ty` is `T`, `assoc_ty` is `Item`.
    AssocTySelect { ty: Box<Ty>, assoc_ty: Id },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TyArgs {
    Positional(Vec<Ty>),
    Named(Map<Id, Ty>),
}

/// A unification variable.
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

#[derive(Debug, Default)]
pub(super) struct TyVarGen {
    next_id: u32,
}

/// A type constructor.
#[derive(Debug, Clone)]
pub struct TyCon {
    /// Name of the type.
    pub(super) id: Id,

    /// Type parameters with bounds.
    pub(super) ty_params: Vec<(Id, Vec<Ty>)>,

    /// Associated types. Currently these can't have bounds.
    #[allow(unused)]
    pub(super) assoc_tys: Set<Id>,

    /// Methods for traits, constructor for sums, fields for products.
    ///
    /// Types can refer to `ty_params` and need to be substituted by the instantiated the types in
    /// `ty_params` before use.
    pub(super) details: TyConDetails,
}

/// A type constructor.
///
/// Types of methods and fields can refer to type parameters of the `TyCon`.
#[derive(Debug, Clone)]
pub(super) enum TyConDetails {
    /// Type constructor is for a trait.
    Trait(TraitDetails),

    /// Type constructor is for a product or sum type definition.
    Type(TypeDetails),

    /// Type is a synonym to this other type.
    ///
    /// For now, type synonyms are not allowed to have type parameters, and the RHS needs to have
    /// kind `*`.
    Synonym(Ty),
}

#[derive(Debug, Clone)]
pub(super) struct TraitDetails {
    /// Methods of the trait, with optional default implementations.
    pub(super) methods: Map<Id, TraitMethod>,

    /// Types implementing the trait.
    ///
    /// For now we don't allow extra context in implementations, e.g.
    /// `impl Debug[T] => Debug[Array[T]]` is not possible, and the implemenhting types can be a
    /// set of type constructors.
    pub(super) implementing_tys: Set<Id>,
}

#[derive(Debug, Clone)]
pub(super) struct TraitMethod {
    pub(super) scheme: Scheme,
    pub(super) fun_decl: ast::L<ast::FunDecl>,
}

#[derive(Debug, Clone)]
pub(super) struct TypeDetails {
    /// Value constructors of the type.
    pub(super) cons: Vec<Id>,
}

/// Types of fields of value constructors. Types may contain quantified types of the type.
// TODO: Why do we need this? Why not use the type scheme from the env?
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum ConFields {
    Unnamed(Vec<Ty>),
    Named(Map<SmolStr, Ty>),
}

/// A predicate, e.g. `I: Iterator[Item = A]`.
#[derive(Debug, Clone)]
pub(super) struct Pred {
    /// Type variable constrained by the predicate.
    ///
    /// `I` in the example.
    pub(super) ty_var: TyVarRef,

    /// Trait of the predicate.
    ///
    /// `Iterator` in the example.
    pub(super) trait_: Id,

    /// Types of the associated types of the trait.
    ///
    /// Not all associated types need to be in the map.
    ///
    /// `{Item = A}`  in the exmaple.
    pub(super) assoc_tys: Map<Id, Ty>,
}

/// A predicate set.
#[derive(Debug, Default, Clone)]
pub(super) struct PredSet {
    /// Maps type variables to traits to associated types of the trait.
    preds: Map<TyVarRef, Map<Id, Map<Id, Ty>>>,
}

impl Scheme {
    /// Instantiate the type scheme, return instantiated predicates and type.
    pub(super) fn instantiate(
        &self,
        level: u32,
        var_gen: &mut TyVarGen,
        preds: &mut PredSet,
        loc: &ast::Loc,
    ) -> Ty {
        // TODO: We should rename type variables in a renaming pass, or disallow shadowing, or
        // handle shadowing here.

        let mut var_map: Map<Id, TyVarRef> = Default::default();

        for (var, bounds) in &self.quantified_vars {
            let instantiated_var = var_gen.new_var(level, self.loc.clone());
            var_map.insert(var.clone(), instantiated_var.clone());

            for (trait_, assoc_tys) in bounds {
                let pred = Pred {
                    ty_var: instantiated_var.clone(),
                    trait_: trait_.clone(),
                    assoc_tys: assoc_tys.clone(),
                };
                preds.add(pred, loc);
            }
        }

        self.ty.subst_qvars(&var_map)
    }

    pub(super) fn instantiate_with_tys(&self, tys: &[Ty]) -> Ty {
        assert_eq!(tys.len(), self.quantified_vars.len());

        let mut ty = self.ty.clone();
        for ((quantified_var, bounds), ty_) in self.quantified_vars.iter().zip(tys.iter()) {
            assert!(bounds.is_empty());
            ty = ty.subst(quantified_var, ty_);
        }

        ty
    }

    /// Substitute `ty` for quantified `var` in `self`.
    pub(super) fn subst(&self, var: &Id, ty: &Ty, _loc: &ast::Loc) -> Scheme {
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
    pub(super) fn eq_modulo_alpha(&self, other: &Scheme) -> bool {
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
            if con1 != con2 {
                return false;
            }

            match (args1, args2) {
                (TyArgs::Positional(args1), TyArgs::Positional(args2)) => {
                    args1.len() == args2.len()
                        && args1
                            .iter()
                            .zip(args2.iter())
                            .all(|(ty1, ty2)| ty_eq_modulo_alpha(ty1, ty2, ty1_qvars, ty2_qvars))
                }

                (TyArgs::Named(args1), TyArgs::Named(args2)) => {
                    let names1: Set<&Id> = args1.keys().collect();
                    let names2: Set<&Id> = args2.keys().collect();

                    if names1 != names2 {
                        return false;
                    }

                    for name in names1 {
                        if !ty_eq_modulo_alpha(
                            args1.get(name).unwrap(),
                            args2.get(name).unwrap(),
                            ty1_qvars,
                            ty2_qvars,
                        ) {
                            return false;
                        }
                    }

                    true
                }

                _ => false,
            }
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
    pub(super) fn unit() -> Ty {
        Ty::Record(Default::default())
    }

    pub(super) fn bool() -> Ty {
        Ty::Con(SmolStr::new_static("Bool"))
    }

    pub(super) fn to_str_view_id() -> Id {
        SmolStr::new_static("ToStrView")
    }

    pub(super) fn str_view() -> Ty {
        Ty::Con(SmolStr::new_static("StrView"))
    }

    /// Substitute `ty` for quantified `var` in `self`.
    pub(super) fn subst(&self, var: &Id, ty: &Ty) -> Ty {
        match self {
            Ty::Con(id) => Ty::Con(id.clone()),

            Ty::Var(var) => Ty::Var(var.clone()),

            Ty::App(var, args) => Ty::App(
                var.clone(),
                match args {
                    TyArgs::Positional(tys) => {
                        TyArgs::Positional(tys.iter().map(|arg_ty| arg_ty.subst(var, ty)).collect())
                    }
                    TyArgs::Named(tys) => TyArgs::Named(
                        tys.iter()
                            .map(|(name, arg_ty)| (name.clone(), arg_ty.subst(var, ty)))
                            .collect(),
                    ),
                },
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

            Ty::AssocTySelect { ty, assoc_ty } => Ty::AssocTySelect {
                ty: Box::new(ty.subst(var, ty)),
                assoc_ty: assoc_ty.clone(),
            },
        }
    }

    pub(super) fn subst_qvars(&self, vars: &Map<Id, TyVarRef>) -> Ty {
        match self {
            Ty::Con(con) => Ty::Con(con.clone()),

            Ty::Var(var) => Ty::Var(var.clone()),

            Ty::App(ty, tys) => Ty::App(
                ty.clone(),
                match tys {
                    TyArgs::Positional(tys) => {
                        TyArgs::Positional(tys.iter().map(|ty| ty.subst_qvars(vars)).collect())
                    }
                    TyArgs::Named(tys) => TyArgs::Named(
                        tys.iter()
                            .map(|(name, ty)| (name.clone(), ty.subst_qvars(vars)))
                            .collect(),
                    ),
                },
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

            Ty::AssocTySelect { ty, assoc_ty } => Ty::AssocTySelect {
                ty: Box::new(ty.subst_qvars(vars)),
                assoc_ty: assoc_ty.clone(),
            },
        }
    }

    /// If the type is a unification variable, follow the links.
    ///
    /// Otherwise returns the original type.
    pub(super) fn normalize(&self) -> Ty {
        match self {
            Ty::Var(var_ref) => var_ref.normalize(),
            other => other.clone(),
        }
    }

    /// Get the type constructor of the type and the type arguments.
    pub fn con(&self) -> Option<(Id, TyArgs)> {
        match self.normalize() {
            Ty::Con(con) => Some((con.clone(), TyArgs::empty())),

            Ty::App(con, args) => Some((con.clone(), args.clone())),

            Ty::Var(_)
            | Ty::Record(_)
            | Ty::QVar(_)
            | Ty::Fun(_, _)
            | Ty::FunNamedArgs(_, _)
            | Ty::AssocTySelect { .. } => None,
        }
    }

    pub(super) fn is_void(&self) -> bool {
        match self {
            Ty::Con(con) => con == &SmolStr::new_static("Void"),
            _ => false,
        }
    }
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
    pub(super) fn id(&self) -> u32 {
        self.0.id
    }

    pub(super) fn level(&self) -> u32 {
        self.0.level.get()
    }

    pub(super) fn link(&self) -> Option<Ty> {
        self.0.link.borrow().clone()
    }

    pub(super) fn set_link(&self, ty: Ty) {
        *self.0.link.borrow_mut() = Some(ty);
    }

    pub(super) fn prune_level(&self, level: u32) {
        let self_level = self.level();
        self.0.level.set(std::cmp::min(level, self_level));
    }

    pub(super) fn normalize(&self) -> Ty {
        let link = match &*self.0.link.borrow() {
            Some(link) => link.normalize(),
            None => return Ty::Var(self.clone()),
        };
        self.set_link(link.clone());
        link
    }
}

impl TyVarGen {
    pub(super) fn new_var(&mut self, level: u32, loc: ast::Loc) -> TyVarRef {
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

impl TyCon {
    pub(super) fn arity(&self) -> u32 {
        self.ty_params.len() as u32
    }

    pub fn is_trait(&self) -> bool {
        matches!(self.details, TyConDetails::Trait { .. })
    }
}

impl TyConDetails {
    pub(super) fn placeholder() -> Self {
        TyConDetails::Type(TypeDetails { cons: vec![] })
    }

    pub(super) fn is_trait(&self) -> bool {
        matches!(self, TyConDetails::Trait(_))
    }
}

impl TyArgs {
    pub(super) fn empty() -> Self {
        TyArgs::Positional(vec![])
    }
}

impl PredSet {
    pub(super) fn add(&mut self, pred: Pred, loc: &ast::Loc) {
        let Pred {
            ty_var,
            trait_,
            assoc_tys,
        } = pred;

        let trait_map = self.preds.entry(ty_var.clone()).or_default();

        // TODO: Give unification variables
        let old = trait_map.insert(trait_.clone(), assoc_tys);
        if old.is_some() {
            panic!(
                "{}: Type variable {:?} already has a constraint on trait {}",
                loc_string(loc),
                ty_var,
                trait_
            );
        }
    }

    #[allow(unused)]
    pub(super) fn into_preds(mut self) -> Vec<Pred> {
        let mut preds: Vec<Pred> = vec![];
        for (ty_var, trait_map) in self.preds.drain() {
            for (trait_, assoc_tys) in trait_map {
                preds.push(Pred {
                    ty_var: ty_var.clone(),
                    trait_,
                    assoc_tys,
                });
            }
        }
        preds
    }
}
