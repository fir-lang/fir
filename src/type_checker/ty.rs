//! Syntax for type checking types.

use crate::ast::{self, Id};
use crate::collections::{Map, ScopeMap, Set};
use crate::type_checker::loc_display;

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use smol_str::SmolStr;

/// A type scheme.
#[derive(Debug, Clone)]
pub struct Scheme {
    /// Generalized variables with bounds.
    pub(super) quantified_vars: Vec<(Id, QVar)>,

    /// The generalized type.
    // TODO: Should we have separate fields for arguments types and return type?
    pub(super) ty: Ty,

    /// Source code location of the variable with this type scheme. This is used in error messages
    /// and for debugging.
    pub(super) loc: ast::Loc,
}

/// Kind and bounds of a quantified type variable.
#[derive(Debug, Clone)]
pub struct QVar {
    pub kind: Kind,

    /// Bounds of the variable. E.g. in `I: ToStr + Iterator[Item = A]`:
    /// ```ignore
    /// {
    ///     (ToStr => {}),
    ///     (Iterator => {Item = A}),
    /// }
    /// ```
    pub bounds: Map<Id, Map<Id, Ty>>,
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

    /// Only in type schemes: a quantified type variable.
    ///
    /// Instantiation converts these into unification variables (`Ty::Var`).
    QVar(Id),

    /// A function type, e.g. `Fn(U32): Str`, `Fn(x: U32, y: U32): T`.
    Fun { args: FunArgs, ret: Box<Ty> },

    /// Select an associated type of a type, e.g. in `T.Item` `ty` is `T`, `assoc_ty` is `Item`.
    AssocTySelect { ty: Box<Ty>, assoc_ty: Id },

    /// An anonymous record or variant type or row type. E.g. `(a: Str, ..R)`, `[Err1(Str), ..R]`.
    Anonymous {
        labels: Map<Id, Ty>,

        /// Row extension. See `Extension` documentation.
        extension: Extension,

        kind: RecordOrVariant,

        /// Whether this is a row type. A row type has its own kind `row`. When not a row, the type
        /// has kind `*`.
        is_row: bool,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecordOrVariant {
    Record,
    Variant,
}

/// A row extension for a `Ty::Record`, `Ty::Variant` or `Ty::Row`.
///
/// When available, this will be one of:
///
/// - `Ty::Var`: a unification variable.
/// - `Ty::Con`: a rigid type variable.
/// - `Ty::Row`: an extension.
type Extension = Option<Box<Ty>>;

// Q: Same type as `TyArgs`, should we use the same type?
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FunArgs {
    Positional(Vec<Ty>),
    Named(Map<Id, Ty>),
}

impl FunArgs {
    pub fn len(&self) -> usize {
        match self {
            FunArgs::Positional(args) => args.len(),
            FunArgs::Named(args) => args.len(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TyArgs {
    Positional(Vec<Ty>),
    Named(Map<Id, Ty>),
}

/// A reference to a unification variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TyVarRef(Rc<TyVar>);

impl TyVarRef {
    #[allow(unused)]
    pub(super) fn loc(&self) -> ast::Loc {
        self.0.loc.clone()
    }
}

/// A unification variable.
#[derive(Debug, Clone)]
pub struct TyVar {
    /// Identity of the unification variable.
    ///
    /// This is used to compare unification variables for equality.
    id: u32,

    /// Kind of the variable.
    kind: Kind,

    /// Depth of the scope the unification variable was craeted in.
    level: Cell<u32>,

    /// When unified with a type, this holds the type.
    link: RefCell<Option<Ty>>,

    /// Source code location of the type scheme that generated this type variable. This is used in
    /// error messages and for debugging.
    loc: ast::Loc,
}

/// Kind of a unification variable.
///
/// We don't support higher-kinded variables yet, so this is either a `*` or `row` for now.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Kind {
    Star,
    Row(RecordOrVariant),
}

#[derive(Debug, Default)]
pub(super) struct TyVarGen {
    next_id: u32,
}

/// A type constructor.
#[derive(Debug, Clone)]
pub struct TyCon {
    /// Name of the type.
    pub id: Id,

    /// Type parameters with bounds.
    ///
    /// E.g. in `[A: Iterator[Item = B]]`, this is `[(A, {Iterator => {Item => B}})]`.
    pub(super) ty_params: Vec<(Id, Map<Id, Map<Id, Ty>>)>,

    /// Associated types. Currently these can't have bounds.
    // TODO: This should be `Trait -> Assoc type -> Ty` to allow same associated types in different
    // traits.
    pub(super) assoc_tys: Map<Id, Ty>,

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

    /// Associated types of the trait.
    pub(super) assoc_tys: Set<Id>,

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
    pub(super) cons: Vec<ConShape>,
}

// TODO: Probably make this an enum with `product` and `sum` variants.
#[derive(Debug, Clone)]
pub(super) struct ConShape {
    pub(super) name: Option<Id>,
    pub(super) fields: ConFieldShape,
}

#[derive(Debug, Clone)]
pub(super) enum ConFieldShape {
    Unnamed(u32),
    Named(Set<Id>),
}

/// Types of fields of value constructors. Types may contain quantified types of the type.
// TODO: Why do we need this? Why not use the type scheme from the env?
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum ConFields {
    Unnamed(Vec<Ty>),
    Named(Map<Id, Ty>),
}

/// A predicate, e.g. `I: Iterator[Item = A]`.
#[derive(Debug, Clone)]
pub(super) struct Pred {
    /// Type variable constrained by the predicate.
    ///
    /// `I` in the example.
    ///
    /// Note: location of this type variable is the declaration in the function definition, not the
    /// use site that instantiated it.
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

    /// Location of the expression that created this predicate.
    pub(super) loc: ast::Loc,
}

/// A predicate set.
#[derive(Debug, Default, Clone)]
pub(super) struct PredSet {
    /// Maps type variables to traits to associated types of the trait.
    preds: Map<TyVarRef, Map<Id, TraitBoundDetails>>,
}

// E.g. `Item = A` in `Iterator[Item = A]`.
pub(super) type AssocTyMap = Map<Id, Ty>;

#[derive(Debug, Clone)]
pub(super) struct TraitBoundDetails {
    /// Associated types of the bound. E.g. `Item = A` in `X: Iterator[Item = A]`.
    pub(super) assoc_tys: AssocTyMap,

    /// Location of the expression that generated the bound.
    pub(super) loc: ast::Loc,
}

impl Scheme {
    /// Instantiate the type scheme, return instantiated predicates and type.
    pub(super) fn instantiate(
        &self,
        level: u32,
        var_gen: &mut TyVarGen,
        preds: &mut PredSet,
        loc: &ast::Loc,
    ) -> (Ty, Vec<TyVarRef>) {
        // TODO: We should rename type variables in a renaming pass, or disallow shadowing, or
        // handle shadowing here.

        let mut var_map: Map<Id, Ty> = Default::default();
        let mut instantiations: Vec<TyVarRef> = Vec::with_capacity(self.quantified_vars.len());

        // Instantiate quantified variables of the scheme.
        for (qvar, QVar { kind, bounds: _ }) in &self.quantified_vars {
            let instantiated_var = var_gen.new_var(level, kind.clone(), self.loc.clone());
            var_map.insert(qvar.clone(), Ty::Var(instantiated_var.clone()));
            instantiations.push(instantiated_var);
        }

        // Add associated types, substitute instantiated types.
        for (instantiation, (_qvar, QVar { kind: _, bounds })) in
            instantiations.iter().zip(self.quantified_vars.iter())
        {
            for (trait_, assoc_tys) in bounds.iter() {
                let pred = Pred {
                    ty_var: instantiation.clone(),
                    trait_: trait_.clone(),
                    assoc_tys: assoc_tys
                        .iter()
                        .map(|(assoc_ty, ty)| (assoc_ty.clone(), ty.subst_qvars(&var_map)))
                        .collect(),
                    loc: loc.clone(),
                };
                preds.add(pred);
            }
        }

        (self.ty.subst_qvars(&var_map), instantiations)
    }

    pub(super) fn instantiate_with_tys(&self, arg_tys: &[Ty]) -> Ty {
        assert!(self.quantified_vars.len() == arg_tys.len());
        let mut var_map: Map<Id, Ty> =
            Map::with_capacity_and_hasher(self.quantified_vars.len(), Default::default());
        for ((qvar, _), arg) in self.quantified_vars.iter().zip(arg_tys.iter()) {
            var_map.insert(qvar.clone(), arg.clone());
        }
        self.ty.subst_qvars(&var_map)
    }

    /// Substitute `ty` for quantified `var` in `self`.
    pub(super) fn subst(&self, var: &Id, ty: &Ty, _loc: &ast::Loc) -> Scheme {
        // TODO: This is a bit hacky.. In top-level functions `var` should be in `quantified_vars`,
        // but in associated functions and trait methods it can also be a type parameter of the
        // trait/type. For now we use the same subst method for both.
        debug_assert!(self.quantified_vars.iter().any(|(qvar, _)| qvar == var));

        Scheme {
            quantified_vars: self
                .quantified_vars
                .iter()
                .filter(|(qvar, _)| qvar != var)
                .cloned()
                .collect(),
            ty: self.ty.subst(var, ty),
            loc: self.loc.clone(),
        }
    }

    /// Substitute `ty` for the `Self` type in the scheme.
    pub(super) fn subst_self(&self, ty: &Ty) -> Scheme {
        Scheme {
            quantified_vars: self.quantified_vars.clone(),
            ty: self.ty.subst_self(ty),
            loc: self.loc.clone(),
        }
    }

    /// Compare two schemes for equality modulo alpha renaming of quantified types.
    ///
    /// `extra_qvars` are quantified variables that can appear in both of the types in the same
    /// places.
    pub(super) fn eq_modulo_alpha(
        &self,
        cons: &ScopeMap<Id, TyCon>,
        extra_qvars: &Set<Id>,
        other: &Scheme,
        loc: &ast::Loc,
    ) -> bool {
        if self.quantified_vars.len() != other.quantified_vars.len() {
            return false;
        }

        // Map quantified variables to their indices.
        let left_vars: Map<Id, u32> = self
            .quantified_vars
            .iter()
            .enumerate()
            .map(|(i, (qvar, _))| (qvar.clone(), i as u32))
            .collect();

        let right_vars: Map<Id, u32> = other
            .quantified_vars
            .iter()
            .enumerate()
            .map(|(i, (qvar, _))| (qvar.clone(), i as u32))
            .collect();

        ty_eq_modulo_alpha(
            cons,
            extra_qvars,
            &self.ty,
            &other.ty,
            &left_vars,
            &right_vars,
            loc,
        )
    }
}

fn ty_eq_modulo_alpha(
    cons: &ScopeMap<Id, TyCon>,
    extra_qvars: &Set<Id>,
    ty1: &Ty,
    ty2: &Ty,
    ty1_qvars: &Map<Id, u32>,
    ty2_qvars: &Map<Id, u32>,
    loc: &ast::Loc,
) -> bool {
    let ty1_normalized = ty1.normalize(cons);
    let ty2_normalized = ty2.normalize(cons);
    match (&ty1_normalized, &ty2_normalized) {
        (Ty::Con(con1), Ty::Con(con2)) => con1 == con2,

        (Ty::Var(_), _) | (_, Ty::Var(_)) => panic!("Unification variable in ty_eq_modulo_alpha"),

        (Ty::App(con1, args1), Ty::App(con2, args2)) => {
            if con1 != con2 {
                return false;
            }

            match (args1, args2) {
                (TyArgs::Positional(args1), TyArgs::Positional(args2)) => {
                    args1.len() == args2.len()
                        && args1.iter().zip(args2.iter()).all(|(ty1, ty2)| {
                            ty_eq_modulo_alpha(
                                cons,
                                extra_qvars,
                                ty1,
                                ty2,
                                ty1_qvars,
                                ty2_qvars,
                                loc,
                            )
                        })
                }

                (TyArgs::Named(args1), TyArgs::Named(args2)) => {
                    let names1: Set<&Id> = args1.keys().collect();
                    let names2: Set<&Id> = args2.keys().collect();

                    if names1 != names2 {
                        return false;
                    }

                    for name in names1 {
                        if !ty_eq_modulo_alpha(
                            cons,
                            extra_qvars,
                            args1.get(name).unwrap(),
                            args2.get(name).unwrap(),
                            ty1_qvars,
                            ty2_qvars,
                            loc,
                        ) {
                            return false;
                        }
                    }

                    true
                }

                _ => false,
            }
        }

        (
            Ty::Anonymous {
                labels: labels1,
                extension: extension1,
                kind: kind1,
                is_row: is_row1,
            },
            Ty::Anonymous {
                labels: labels2,
                extension: extension2,
                kind: kind2,
                is_row: is_row2,
            },
        ) => {
            assert_eq!(is_row1, is_row2);

            if kind1 != kind2 {
                return false;
            }

            let (labels1, extension1) = crate::type_checker::row_utils::collect_rows(
                cons,
                ty1,
                *kind1,
                labels1,
                extension1.clone(),
            );

            let (labels2, extension2) = crate::type_checker::row_utils::collect_rows(
                cons,
                ty2,
                *kind2,
                labels2,
                extension2.clone(),
            );

            if labels1.keys().collect::<Set<_>>() != labels2.keys().collect() {
                return false;
            }

            for (label1, ty1) in labels1 {
                let ty2 = labels2.get(&label1).unwrap();
                if !ty_eq_modulo_alpha(cons, extra_qvars, &ty1, ty2, ty1_qvars, ty2_qvars, loc) {
                    return false;
                }
            }

            match (extension1, extension2) {
                (None, Some(_)) | (Some(_), None) => false,

                (None, None) => true,

                (Some(ext1), Some(ext2)) => {
                    ty_eq_modulo_alpha(cons, extra_qvars, &ext1, &ext2, ty1_qvars, ty2_qvars, loc)
                }
            }
        }

        (Ty::QVar(qvar1), Ty::QVar(qvar2)) => {
            if qvar1 == qvar2 && extra_qvars.contains(qvar1) {
                return true;
            }

            let qvar1_idx = ty1_qvars.get(qvar1).unwrap_or_else(|| {
                panic!(
                    "{}: BUG: ty_eq_modulo_alpha: Quantified type variable {:?} is not in the set {:?} or {:?}",
                    loc_display(loc), qvar1, ty1_qvars, extra_qvars
                )
            });
            let qvar2_idx = ty2_qvars.get(qvar2).unwrap_or_else(|| {
                panic!(
                    "{}: BUG: ty_eq_modulo_alpha: Quantified type variable {:?} is not in the set {:?} or {:?}",
                    loc_display(loc), qvar2, ty2_qvars, extra_qvars
                )
            });
            qvar1_idx == qvar2_idx
        }

        (
            Ty::Fun {
                args: args1,
                ret: ret1,
            },
            Ty::Fun {
                args: args2,
                ret: ret2,
            },
        ) => {
            if args1.len() != args2.len() {
                return false;
            }

            match (args1, args2) {
                (FunArgs::Positional(args1), FunArgs::Positional(args2)) => {
                    for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                        if !ty_eq_modulo_alpha(
                            cons,
                            extra_qvars,
                            arg1,
                            arg2,
                            ty1_qvars,
                            ty2_qvars,
                            loc,
                        ) {
                            return false;
                        }
                    }
                }

                (FunArgs::Named(args1), FunArgs::Named(args2)) => {
                    let names1: Set<&Id> = args1.keys().collect();
                    let names2: Set<&Id> = args2.keys().collect();

                    if names1 != names2 {
                        return false;
                    }

                    for name in names1 {
                        let ty1 = args1.get(name).unwrap();
                        let ty2 = args2.get(name).unwrap();
                        if !ty_eq_modulo_alpha(
                            cons,
                            extra_qvars,
                            ty1,
                            ty2,
                            ty1_qvars,
                            ty2_qvars,
                            loc,
                        ) {
                            return false;
                        }
                    }
                }

                (FunArgs::Named(_), FunArgs::Positional(_))
                | (FunArgs::Positional(_), FunArgs::Named(_)) => return false,
            }

            ty_eq_modulo_alpha(cons, extra_qvars, ret1, ret2, ty1_qvars, ty2_qvars, loc)
        }

        _ => false,
    }
}

impl Ty {
    pub(super) fn unit() -> Ty {
        Ty::Anonymous {
            labels: Default::default(),
            extension: None,
            kind: RecordOrVariant::Record,
            is_row: false,
        }
    }

    #[allow(unused)]
    pub(super) fn empty_variant() -> Ty {
        Ty::Anonymous {
            labels: Default::default(),
            extension: None,
            kind: RecordOrVariant::Variant,
            is_row: false,
        }
    }

    pub(super) fn bool() -> Ty {
        Ty::Con(SmolStr::new_static("Bool"))
    }

    pub(super) fn to_str_id() -> Id {
        SmolStr::new_static("ToStr")
    }

    pub(super) fn str() -> Ty {
        Ty::Con(SmolStr::new_static("Str"))
    }

    pub(super) fn char() -> Ty {
        Ty::Con(SmolStr::new_static("Char"))
    }

    /// Substitute `ty` for quantified `var` in `self`.
    pub(super) fn subst(&self, var: &Id, ty: &Ty) -> Ty {
        match self {
            Ty::Con(id) => Ty::Con(id.clone()),

            Ty::Var(var) => Ty::Var(var.clone()),

            Ty::App(con, args) => Ty::App(
                con.clone(),
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

            Ty::Anonymous {
                labels,
                extension,
                kind,
                is_row,
            } => Ty::Anonymous {
                labels: labels
                    .iter()
                    .map(|(field, field_ty)| (field.clone(), field_ty.subst(var, ty)))
                    .collect(),
                extension: extension.as_ref().map(|ext| Box::new(ext.subst(var, ty))),
                kind: *kind,
                is_row: *is_row,
            },

            Ty::QVar(qvar) => {
                if qvar == var {
                    ty.clone()
                } else {
                    Ty::QVar(qvar.clone())
                }
            }

            Ty::Fun { args, ret } => Ty::Fun {
                args: match args {
                    FunArgs::Positional(args) => FunArgs::Positional(
                        args.iter().map(|arg_ty| arg_ty.subst(var, ty)).collect(),
                    ),
                    FunArgs::Named(args) => FunArgs::Named(
                        args.iter()
                            .map(|(name, arg_ty)| (name.clone(), arg_ty.subst(var, ty)))
                            .collect(),
                    ),
                },
                ret: Box::new(ret.subst(var, ty)),
            },

            Ty::AssocTySelect { ty, assoc_ty } => Ty::AssocTySelect {
                ty: Box::new(ty.subst(var, ty)),
                assoc_ty: assoc_ty.clone(),
            },
        }
    }

    /// Substitute `ty` for the `Self` type in the type.
    fn subst_self(&self, self_ty: &Ty) -> Ty {
        match self {
            Ty::Con(id) => {
                if id == &SmolStr::new_static("Self") {
                    self_ty.clone()
                } else {
                    Ty::Con(id.clone())
                }
            }

            Ty::Var(var) => Ty::Var(var.clone()),

            Ty::App(ty, tys) => Ty::App(
                ty.clone(),
                match tys {
                    TyArgs::Positional(tys) => {
                        TyArgs::Positional(tys.iter().map(|ty| ty.subst_self(self_ty)).collect())
                    }
                    TyArgs::Named(tys) => TyArgs::Named(
                        tys.iter()
                            .map(|(name, ty)| (name.clone(), ty.subst_self(self_ty)))
                            .collect(),
                    ),
                },
            ),

            Ty::Anonymous {
                labels,
                extension,
                kind,
                is_row,
            } => Ty::Anonymous {
                labels: labels
                    .iter()
                    .map(|(field_id, field_ty)| (field_id.clone(), field_ty.subst_self(self_ty)))
                    .collect(),
                extension: extension
                    .as_ref()
                    .map(|ext| Box::new(ext.subst_self(self_ty))),
                kind: *kind,
                is_row: *is_row,
            },

            Ty::QVar(id) => Ty::QVar(id.clone()),

            Ty::Fun { args, ret } => Ty::Fun {
                args: match args {
                    FunArgs::Positional(args) => FunArgs::Positional(
                        args.iter().map(|arg| arg.subst_self(self_ty)).collect(),
                    ),
                    FunArgs::Named(args) => FunArgs::Named(
                        args.iter()
                            .map(|(name, ty_)| (name.clone(), ty_.subst_self(self_ty)))
                            .collect(),
                    ),
                },
                ret: Box::new(ret.subst_self(self_ty)),
            },

            Ty::AssocTySelect { ty, assoc_ty } => Ty::AssocTySelect {
                ty: Box::new(ty.subst_self(self_ty)),
                assoc_ty: assoc_ty.clone(),
            },
        }
    }

    pub(super) fn subst_qvars(&self, vars: &Map<Id, Ty>) -> Ty {
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

            Ty::Anonymous {
                labels,
                extension,
                kind,
                is_row,
            } => Ty::Anonymous {
                labels: labels
                    .iter()
                    .map(|(label_id, label_ty)| (label_id.clone(), label_ty.subst_qvars(vars)))
                    .collect(),
                extension: extension
                    .as_ref()
                    .map(|ext| Box::new(ext.subst_qvars(vars))),
                kind: *kind,
                is_row: *is_row,
            },

            Ty::QVar(id) => vars
                .get(id)
                .cloned()
                .unwrap_or_else(|| panic!("subst_qvars: unbound QVar {}", id)),

            Ty::Fun { args, ret } => Ty::Fun {
                args: match args {
                    FunArgs::Positional(args) => {
                        FunArgs::Positional(args.iter().map(|arg| arg.subst_qvars(vars)).collect())
                    }
                    FunArgs::Named(args) => FunArgs::Named(
                        args.iter()
                            .map(|(name, ty)| (name.clone(), ty.subst_qvars(vars)))
                            .collect(),
                    ),
                },
                ret: Box::new(ret.subst_qvars(vars)),
            },

            Ty::AssocTySelect { ty, assoc_ty } => Ty::AssocTySelect {
                ty: Box::new(ty.subst_qvars(vars)),
                assoc_ty: assoc_ty.clone(),
            },
        }
    }

    /// If the type is a unification variable, follow the links.
    ///
    /// Otherwise returns the original type.
    pub(super) fn normalize(&self, cons: &ScopeMap<Id, TyCon>) -> Ty {
        match self {
            Ty::Var(var_ref) => var_ref.normalize(cons),

            Ty::Con(con) => match cons.get(con) {
                Some(ty_con) => match &ty_con.details {
                    TyConDetails::Synonym(ty) => ty.clone(),
                    TyConDetails::Trait(_) | TyConDetails::Type(_) => self.clone(),
                },
                None => self.clone(),
            },

            Ty::AssocTySelect { ty, assoc_ty } => match ty.normalize(cons) {
                Ty::Con(con) | Ty::App(con, _) => {
                    let con = cons
                        .get(&con)
                        .unwrap_or_else(|| panic!("Unknown type constructor {}", con));
                    match con.assoc_tys.get(assoc_ty) {
                        Some(ty) => ty.clone(),
                        None => panic!(
                            "Associated type {} is not defined for type {}",
                            assoc_ty, con.id
                        ),
                    }
                }
                ty => Ty::AssocTySelect {
                    ty: Box::new(ty),
                    assoc_ty: assoc_ty.clone(),
                },
            },

            _ => self.clone(),
        }
    }

    /// Same as `normalize` but normalizes type arguments as well.
    pub(super) fn deep_normalize(&self, cons: &ScopeMap<Id, TyCon>) -> Ty {
        match self {
            Ty::Var(var_ref) => var_ref.normalize(cons),

            Ty::Con(con) => match cons.get(con) {
                Some(ty_con) => match &ty_con.details {
                    TyConDetails::Synonym(ty) => ty.clone(),
                    TyConDetails::Trait(_) | TyConDetails::Type(_) => self.clone(),
                },
                None => self.clone(),
            },

            Ty::App(con, args) => Ty::App(
                con.clone(),
                match args {
                    TyArgs::Positional(tys) => {
                        TyArgs::Positional(tys.iter().map(|ty| ty.deep_normalize(cons)).collect())
                    }
                    TyArgs::Named(tys) => TyArgs::Named(
                        tys.iter()
                            .map(|(name, ty)| (name.clone(), ty.deep_normalize(cons)))
                            .collect(),
                    ),
                },
            ),

            Ty::Anonymous {
                labels,
                extension,
                kind,
                is_row,
            } => {
                let (labels, extension) = crate::type_checker::row_utils::collect_rows(
                    cons,
                    self,
                    *kind,
                    labels,
                    extension.clone(),
                );
                Ty::Anonymous {
                    labels,
                    extension: extension.map(Box::new),
                    kind: *kind,
                    is_row: *is_row,
                }
            }

            Ty::Fun { args, ret } => Ty::Fun {
                args: match args {
                    FunArgs::Positional(args) => FunArgs::Positional(
                        args.iter().map(|arg| arg.deep_normalize(cons)).collect(),
                    ),
                    FunArgs::Named(args) => FunArgs::Named(
                        args.iter()
                            .map(|(name, arg)| (name.clone(), arg.deep_normalize(cons)))
                            .collect(),
                    ),
                },
                ret: Box::new(ret.deep_normalize(cons)),
            },

            Ty::AssocTySelect { ty, assoc_ty } => Ty::AssocTySelect {
                ty: Box::new(ty.deep_normalize(cons)),
                assoc_ty: assoc_ty.clone(),
            },

            Ty::QVar(_) => panic!(),
        }
    }

    /// Get the type constructor of the type and the type arguments.
    pub fn con(&self, cons: &ScopeMap<Id, TyCon>) -> Option<(Id, TyArgs)> {
        match self.normalize(cons) {
            Ty::Con(con) => Some((con.clone(), TyArgs::empty())),

            Ty::App(con, args) => Some((con.clone(), args.clone())),

            Ty::Var(_)
            | Ty::Anonymous { .. }
            | Ty::QVar(_)
            | Ty::Fun { .. }
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

    pub fn kind(&self) -> Kind {
        self.0.kind.clone()
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

    pub(super) fn normalize(&self, cons: &ScopeMap<Id, TyCon>) -> Ty {
        let link = match &*self.0.link.borrow() {
            Some(link) => link.normalize(cons).deep_normalize(cons),
            None => return Ty::Var(self.clone()),
        };
        self.set_link(link.clone());
        link
    }
}

impl TyVarGen {
    pub(super) fn new_var(&mut self, level: u32, kind: Kind, loc: ast::Loc) -> TyVarRef {
        let id = self.next_id;
        self.next_id += 1;
        TyVarRef(Rc::new(TyVar {
            id,
            level: Cell::new(level),
            link: RefCell::new(None),
            loc,
            kind,
        }))
    }
}

impl TyCon {
    pub(super) fn opaque(id: Id) -> TyCon {
        TyCon {
            id,
            ty_params: vec![],
            assoc_tys: Default::default(),
            details: TyConDetails::Type(TypeDetails { cons: vec![] }),
        }
    }

    pub(super) fn arity(&self) -> u32 {
        self.ty_params.len() as u32
    }

    pub fn is_trait(&self) -> bool {
        self.details.is_trait()
    }

    pub(super) fn trait_details(&self) -> Option<&TraitDetails> {
        self.details.trait_details()
    }

    pub(super) fn con_details(&self) -> Option<&[ConShape]> {
        self.details.con_details()
    }
}

impl TyConDetails {
    pub(super) fn is_trait(&self) -> bool {
        self.trait_details().is_some()
    }

    pub(super) fn trait_details(&self) -> Option<&TraitDetails> {
        match self {
            TyConDetails::Trait(details) => Some(details),
            _ => None,
        }
    }

    pub(super) fn con_details(&self) -> Option<&[ConShape]> {
        match self {
            TyConDetails::Type(TypeDetails { cons }) => Some(cons),
            _ => None,
        }
    }
}

impl TyArgs {
    pub(super) fn empty() -> Self {
        TyArgs::Positional(vec![])
    }
}

impl PredSet {
    pub(super) fn add(&mut self, pred: Pred) {
        let Pred {
            ty_var,
            trait_,
            assoc_tys,
            loc,
        } = pred;
        let trait_map = self.preds.entry(ty_var.clone()).or_default();
        let bound_details = TraitBoundDetails {
            assoc_tys,
            loc: loc.clone(),
        };
        let old = trait_map.insert(trait_.clone(), bound_details);
        if old.is_some() {
            panic!(
                "{}: Type variable {:?} already has a constraint on trait {}",
                loc_display(&loc),
                ty_var,
                trait_
            );
        }
    }

    pub(super) fn into_preds(mut self) -> Vec<Pred> {
        let mut preds: Vec<Pred> = vec![];
        for (ty_var, trait_map) in self.preds.drain() {
            for (trait_, TraitBoundDetails { assoc_tys, loc }) in trait_map {
                preds.push(Pred {
                    ty_var: ty_var.clone(),
                    trait_,
                    assoc_tys,
                    loc,
                });
            }
        }
        preds
    }
}

impl ConShape {
    pub(super) fn from_ast(con: &ast::ConstructorDecl) -> ConShape {
        let ast::ConstructorDecl { name, fields } = con;
        ConShape {
            name: Some(name.clone()),
            fields: ConFieldShape::from_ast(fields),
        }
    }
}

impl ConFieldShape {
    pub(super) fn from_ast(fields: &ast::ConstructorFields) -> ConFieldShape {
        match fields {
            ast::ConstructorFields::Empty => ConFieldShape::Unnamed(0),
            ast::ConstructorFields::Unnamed(fields) => ConFieldShape::Unnamed(fields.len() as u32),
            ast::ConstructorFields::Named(fields) => {
                ConFieldShape::Named(fields.iter().map(|(k, _)| k.clone()).collect())
            }
        }
    }
}

use std::fmt;

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Con(id) => write!(f, "{}", id),

            Ty::Var(var_ref) => write!(f, "_{}", var_ref.id()),

            Ty::App(id, args) => {
                write!(f, "{}[", id)?;
                match args {
                    TyArgs::Positional(tys) => {
                        for (i, ty) in tys.iter().enumerate() {
                            if i > 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{}", ty)?;
                        }
                    }
                    TyArgs::Named(tys) => {
                        for (i, (name, ty)) in tys.iter().enumerate() {
                            if i > 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{} = {}", name, ty)?;
                        }
                    }
                }
                write!(f, "]")
            }

            Ty::Anonymous {
                labels,
                extension,
                kind,
                is_row,
            } => {
                let (left_delim, right_delim) = match kind {
                    RecordOrVariant::Record => ('(', ')'),
                    RecordOrVariant::Variant => ('[', ']'),
                };

                if *is_row {
                    write!(f, "row")?;
                }

                write!(f, "{}", left_delim)?;
                for (i, (label_id, label_ty)) in labels.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", label_id, label_ty)?;
                }
                if let Some(ext) = extension {
                    if !labels.is_empty() {
                        write!(f, ", ")?;
                    }
                    write!(f, "..{}", ext)?;
                }
                write!(f, "{}", right_delim)
            }

            Ty::QVar(id) => write!(f, "'{}", id),

            Ty::Fun { args, ret } => {
                write!(f, "Fn(")?;
                match args {
                    FunArgs::Positional(args) => {
                        for (i, arg) in args.iter().enumerate() {
                            if i > 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{}", arg)?;
                        }
                    }
                    FunArgs::Named(args) => {
                        for (i, (name, ty)) in args.iter().enumerate() {
                            if i > 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{}: {}", name, ty)?;
                        }
                    }
                }
                write!(f, "): {}", ret)
            }

            Ty::AssocTySelect { ty, assoc_ty } => {
                write!(f, "{}.{}", ty, assoc_ty)
            }
        }
    }
}

impl fmt::Display for Scheme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.quantified_vars.is_empty() {
            write!(f, "[")?;
            for (i, (qvar, QVar { kind: _, bounds })) in self.quantified_vars.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", qvar)?;
                if !bounds.is_empty() {
                    write!(f, ": ")?;
                    for (j, (trait_, assoc_tys)) in bounds.iter().enumerate() {
                        if j > 0 {
                            write!(f, " + ")?;
                        }
                        write!(f, "{}", trait_)?;
                        if !assoc_tys.is_empty() {
                            write!(f, "[")?;
                            for (k, (assoc_ty, ty)) in assoc_tys.iter().enumerate() {
                                if k > 0 {
                                    write!(f, ", ")?;
                                }
                                write!(f, "{} = {}", assoc_ty, ty)?;
                            }
                            write!(f, "]")?;
                        }
                    }
                }
            }
            write!(f, "] ")?;
        }
        write!(f, "{}", self.ty)
    }
}
