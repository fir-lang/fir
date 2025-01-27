#![allow(clippy::enum_variant_names)]

pub mod printer;

use crate::collections::Map;
use crate::interpolation::StringPart;
pub use crate::token::IntKind;
use crate::type_checker::{Kind, Ty};

use std::rc::Rc;

use smol_str::SmolStr;

pub type Id = SmolStr;

/// Things with location information.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct L<T> {
    pub loc: Loc,
    pub node: T,
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct Loc {
    /// Module file path, relative to the working directory.
    pub module: Rc<str>,
    pub line_start: u16,
    pub col_start: u16,
    pub byte_offset_start: u32,
    pub line_end: u16,
    pub col_end: u16,
    pub byte_offset_end: u32,
}

impl Loc {
    pub fn dummy() -> Self {
        Loc {
            module: "".into(),
            line_start: 0,
            col_start: 0,
            byte_offset_start: 0,
            line_end: 0,
            col_end: 0,
            byte_offset_end: 0,
        }
    }
}

impl<T> L<T> {
    pub fn new(module: &Rc<str>, start: lexgen_util::Loc, end: lexgen_util::Loc, node: T) -> Self {
        L {
            loc: Loc::from_lexgen(module, start, end),
            node,
        }
    }

    pub fn map<T2, F>(self, f: F) -> L<T2>
    where
        F: FnOnce(T) -> T2,
    {
        let L { loc, node } = self;
        L { loc, node: f(node) }
    }

    pub fn map_as_ref<T2, F>(&self, f: F) -> L<T2>
    where
        F: FnOnce(&T) -> T2,
    {
        let L { loc, node } = &self;
        L {
            loc: loc.clone(),
            node: f(node),
        }
    }

    pub fn set_node<T2>(&self, node: T2) -> L<T2> {
        L {
            loc: self.loc.clone(),
            node,
        }
    }
}

impl Loc {
    pub fn from_lexgen(module: &Rc<str>, start: lexgen_util::Loc, end: lexgen_util::Loc) -> Self {
        Loc {
            module: module.clone(),
            line_start: start.line as u16,
            col_start: start.col as u16,
            byte_offset_start: start.byte_idx as u32,
            line_end: end.line as u16,
            col_end: end.col as u16,
            byte_offset_end: end.byte_idx as u32,
        }
    }
}

pub type Module = Vec<L<TopDecl>>;

/// A top-level declaration.
#[derive(Debug, Clone)]
pub enum TopDecl {
    /// A type declaration: `type T = ...`.
    Type(L<TypeDecl>),

    /// A function declaration: `fn f(...) = ...`.
    Fun(L<FunDecl>),

    /// An import declaration.
    Import(L<ImportDecl>),

    /// A trait declaration.
    Trait(L<TraitDecl>),

    /// An `impl` block, implementing a trait or associated methods for a type.
    Impl(L<ImplDecl>),
}

/// A type declaration: `type Vec[T] = ...`.
#[derive(Debug, Clone)]
pub struct TypeDecl {
    /// The type name, e.g. `Vec`.
    pub name: Id,

    /// Type parameters, e.g. `[T]`.
    pub type_params: Vec<Id>,

    /// Constructors of the type.
    pub rhs: Option<TypeDeclRhs>,
}

/// Constructors of a type declaration.
#[derive(Debug, Clone)]
pub enum TypeDeclRhs {
    /// A sum type, with more than one constructor.
    Sum(Vec<ConstructorDecl>),

    /// A product type uses the type name as the constructor and only has fields.
    Product(ConstructorFields),
}

/// A sum type constructor.
#[derive(Debug, Clone)]
pub struct ConstructorDecl {
    pub name: Id,
    pub fields: ConstructorFields,
}

#[derive(Debug, Clone)]
pub enum ConstructorFields {
    Empty,
    Named(Vec<(Id, Type)>),
    Unnamed(Vec<Type>),
}

#[derive(Debug, Clone)]
pub enum Type {
    /// A type constructor, potentially applied some number of arguments. E.g. `I32`, `Vec[T]`.
    Named(NamedType),

    /// A type variable.
    ///
    /// We don't have higher-kinded types for now, so type variables cannot be applied.
    Var(Id),

    /// An anonymous record type, e.g. `(x: I32, y: I32)`, `(a: Str, ..R)`.
    Record {
        fields: Vec<Named<Type>>,
        extension: Option<Id>,
    },

    /// An anonymous variant type, e.g. `[Error(msg: Str), Ok, ..R]`.
    Variant {
        alts: Vec<VariantAlt>,
        extension: Option<Id>,
    },

    /// A function type: `Fn(I32): Bool`.
    Fn(FnType),
}

#[derive(Debug, Clone)]
pub struct VariantAlt {
    pub con: Id,
    pub fields: Vec<Named<Type>>,
}

/// A named type, e.g. `I32`, `Vec[I32]`, `Iterator[coll, Str]`.
#[derive(Debug, Clone)]
pub struct NamedType {
    /// Name of the type constructor, e.g. `I32`, `Vec`, `Iterator`.
    pub name: Id,

    /// Arguments of the type constructor.
    pub args: Vec<L<Type>>,
}

#[derive(Debug, Clone)]
pub struct FnType {
    pub args: Vec<L<Type>>,

    /// Optional return type of the function. `()` when omitted.
    pub ret: Option<L<Box<Type>>>,

    /// Same as `FunSig.exceptions`.
    pub exceptions: Option<L<Box<Type>>>,
}

#[derive(Debug, Clone)]
pub struct Named<T> {
    pub name: Option<Id>,
    pub node: T,
}

impl<T> Named<T> {
    pub fn map_as_ref<T2, F>(&self, f: F) -> Named<T2>
    where
        F: FnOnce(&T) -> T2,
    {
        let Named { name, node } = &self;
        Named {
            name: name.clone(),
            node: f(node),
        }
    }
}

/// Type signature part of a function declaration: type parameters, value parameters, exception
/// type, return type.
#[derive(Debug, Clone)]
pub struct FunSig {
    /// Predicates of the function, e.g. in `id[Debug[t]](a: t)` this is `[Debug[t]]`.
    pub context: Context,

    /// Whether the function has a `self` parameter.
    pub self_: SelfParam,

    /// Parameters of the function.
    pub params: Vec<(Id, L<Type>)>,

    /// Optional return type.
    pub return_ty: Option<L<Type>>,

    /// The exception signature. If exists, this will be a variant type. Store as `Type` to make it
    /// easier to process with rest of the types.
    pub exceptions: Option<L<Type>>,
}

#[derive(Debug, Clone)]
pub(crate) enum SelfParam {
    No,
    Implicit,
    Explicit(L<Type>),
}

#[derive(Debug, Clone)]
pub struct FunDecl {
    /// Only in associated functions: the parent type. E.g. `Vec` in `Vec.push(...) = ...`.
    pub parent_ty: Option<L<Id>>,

    /// Name of the function.
    pub name: L<Id>,

    /// Type signature of the function.
    pub sig: FunSig,

    /// Body (code) of the function. Not available in `prim` functions.
    pub body: Option<Vec<L<Stmt>>>,
}

impl FunDecl {
    pub fn num_params(&self) -> u32 {
        (match self.sig.self_ {
            SelfParam::No => 0,
            SelfParam::Implicit | SelfParam::Explicit(_) => 1,
        }) + (self.sig.params.len() as u32)
    }
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Let(LetStmt),
    // LetFn(FunDecl),
    Assign(AssignStmt),
    Expr(L<Expr>),
    For(ForStmt),
    While(WhileStmt),
    WhileLet(WhileLetStmt),
    Break {
        label: Option<Id>,

        /// How many levels of loops to break. Parser initializes this as 0, type checker updates
        /// based on the labels of enclosing loops.
        level: u32,
    },
    Continue {
        label: Option<Id>,

        /// Same as `Break.level`.
        level: u32,
    },
}

/// A let statement: `let x: T = expr`.
#[derive(Debug, Clone)]
pub struct LetStmt {
    pub lhs: L<Pat>,
    pub ty: Option<L<Type>>,
    pub rhs: L<Expr>,
}

#[derive(Debug, Clone)]
pub struct MatchExpr {
    pub scrutinee: Box<L<Expr>>,
    pub alts: Vec<Alt>,
}

#[derive(Debug, Clone)]
pub struct Alt {
    pub pattern: L<Pat>,
    pub guard: Option<L<Expr>>,
    pub rhs: Vec<L<Stmt>>,
}

#[derive(Debug, Clone)]
pub enum Pat {
    /// Matches anything, binds it to variable.
    Var(Id),

    /// Matches a constructor.
    Constr(ConstrPattern),

    /// Matches a variant.
    Variant(VariantPattern),

    Record(Vec<Named<L<Pat>>>),

    /// Underscore, aka. wildcard.
    Ignore,

    /// Matches the string.
    Str(String),

    /// Matches the character.
    Char(char),

    /// Match the prefix, bind the rest. E.g. `"a" .. rest`.
    StrPfx(String, Id),

    /// Or pattern: `<pat1> | <pat2>`.
    Or(Box<L<Pat>>, Box<L<Pat>>),
}

#[derive(Debug, Clone)]
pub struct ConstrPattern {
    pub constr: Constructor,
    pub fields: Vec<Named<L<Pat>>>,

    /// Inferred type arguments of the constructor. Filled in by the type checker.
    pub ty_args: Vec<Ty>,
}

#[derive(Debug, Clone)]
pub struct Constructor {
    pub type_: Id,
    pub constr: Option<Id>,
}

#[derive(Debug, Clone)]
pub struct VariantPattern {
    pub constr: Id,
    pub fields: Vec<Named<L<Pat>>>,
}

#[derive(Debug, Clone)]
pub struct IfExpr {
    // At least one element
    pub branches: Vec<(L<Expr>, Vec<L<Stmt>>)>,
    pub else_branch: Option<Vec<L<Stmt>>>,
}

#[derive(Debug, Clone)]
pub struct AssignStmt {
    pub lhs: L<Expr>,
    pub rhs: L<Expr>,
    pub op: AssignOp,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignOp {
    Eq,
    PlusEq,
    MinusEq,
    StarEq,
}

#[derive(Debug, Clone)]
pub struct ForStmt {
    pub label: Option<Id>,
    pub pat: L<Pat>,
    pub ty: Option<Type>,
    pub expr: L<Expr>,
    pub expr_ty: Option<Ty>, // filled in by the type checker
    pub body: Vec<L<Stmt>>,
}

#[derive(Debug, Clone)]
pub struct WhileStmt {
    pub label: Option<Id>,
    pub cond: L<Expr>,
    pub body: Vec<L<Stmt>>,
}

#[derive(Debug, Clone)]
pub struct WhileLetStmt {
    pub label: Option<Id>,
    pub pat: L<Pat>,
    pub cond: L<Expr>,
    pub body: Vec<L<Stmt>>,
}

#[derive(Debug, Clone)]
pub enum Expr {
    /// A variable: `x`.
    Var(VarExpr),

    /// A constructor: `Vec`, `Bool`, `I32`.
    Constr(ConstrExpr),

    /// A variant application: "`A()", "`ParseError(...)".
    ///
    /// Because "`A" is type checked differently from "`A(1)", we parse variant applications as
    /// `Expr::Variant` instead of `Expr::Call` with a variant as the function.
    Variant(VariantExpr),

    /// A field selection: `<expr>.x` where `x` is a field.
    ///
    /// Parser generates this node for all expression of form `<expr>.<id>`, type checker converts
    /// method selection expressions to `MethodSelect`.
    FieldSelect(FieldSelectExpr),

    /// A method selection: `<expr>.x` where `x` is a method.
    ///
    /// This node is generated by the type checker.
    MethodSelect(MethodSelectExpr),

    /// A constructor selection: `Option.None`.
    ConstrSelect(ConstrSelectExpr),

    /// An associated function or method selection:
    ///
    /// - Associated function: `Vec.withCapacity`.
    /// - Method: `Vec.push`.
    AssocFnSelect(AssocFnSelectExpr),

    /// A function call: `f(a)`.
    Call(CallExpr),

    Int(IntExpr),

    String(Vec<StringPart>),

    Char(char),

    Self_,

    BinOp(BinOpExpr),

    UnOp(UnOpExpr),

    Record(Vec<Named<L<Expr>>>),

    Return(Box<L<Expr>>),

    Match(MatchExpr),

    If(IfExpr),

    Fn(FnExpr),
}

#[derive(Debug, Clone)]
pub struct VarExpr {
    pub id: Id,

    /// Inferred type arguments of the variable. Filled in by the type checker.
    pub ty_args: Vec<Ty>,
}

#[derive(Debug, Clone)]
pub struct ConstrExpr {
    pub id: Id,

    /// Inferred type arguments of the constructor. Filled by the type checker.
    pub ty_args: Vec<Ty>,
}

#[derive(Debug, Clone)]
pub struct VariantExpr {
    pub id: Id,
    pub args: Vec<Named<L<Expr>>>,
}

#[derive(Debug, Clone)]
pub struct CallExpr {
    pub fun: Box<L<Expr>>,
    pub args: Vec<CallArg>,
}

#[derive(Debug, Clone)]
pub struct CallArg {
    pub name: Option<Id>,
    pub expr: L<Expr>,
}

/// A field selection: `<expr>.x`.
#[derive(Debug, Clone)]
pub struct FieldSelectExpr {
    pub object: Box<L<Expr>>,
    pub field: Id,
}

/// A method selection: `<expr>.x`.
#[derive(Debug, Clone)]
pub struct MethodSelectExpr {
    pub object: Box<L<Expr>>,

    /// Type of `object`, filled in by the type checker.
    pub object_ty: Option<Ty>,

    pub method: Id,

    /// Type arguments of the method, filled in by the type checker.
    pub ty_args: Vec<Ty>,
}

/// A constructor selection: `Option.None`.
#[derive(Debug, Clone)]
pub struct ConstrSelectExpr {
    pub ty: Id,
    pub constr: Id,

    /// Inferred type arguments of the constructor. Filled by the type checker.
    pub ty_args: Vec<Ty>,
}

/// An associated function or method selection:
///
/// - Associated function: `Vec.withCapacity`.
/// - Method: `Vec.push`.
#[derive(Debug, Clone)]
pub struct AssocFnSelectExpr {
    pub ty: Id,
    pub member: Id,

    /// Inferred type arguments of the type and assocaited function. Filled in by the type checker.
    pub ty_args: Vec<Ty>,
}

#[derive(Debug, Clone)]
pub struct BinOpExpr {
    pub left: Box<L<Expr>>,
    pub right: Box<L<Expr>>,
    pub op: BinOp,
}

#[derive(Debug, Clone)]
pub struct UnOpExpr {
    pub op: UnOp,
    pub expr: Box<L<Expr>>,
}

#[derive(Debug, Clone)]
pub struct IntExpr {
    /// The digits of the integer, without any prefix ("0x" or "0b") and suffix ("u32" etc.).
    ///
    /// The digits will be parsed during type checking. If the integer doesn't have a suffix,
    /// parsing will be done based on the inferred type of the integer.
    pub text: String,

    /// Suffix of the integer. Initially as parsed. If not available, the type checker updates
    /// this based on the inferred type of the integer.
    pub suffix: Option<IntKind>,

    pub radix: u32,

    /// Filled in by the type checker. The parsed integer.
    ///
    /// This should be the integer value as expected by the interpreter. E.g. `-1u64` should be
    /// `0x00000000000000ff`, instead of `0xffffffffffffffff`.
    pub parsed: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Subtract,
    Equal,
    NotEqual,
    Multiply,
    Divide,
    Lt,
    Gt,
    LtEq,
    GtEq,
    And,
    Or,
    BitAnd,
    BitOr,
    LeftShift,
    RightShift,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Debug, Clone)]
pub struct FnExpr {
    pub sig: FunSig,
    pub body: Vec<L<Stmt>>,
    pub idx: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportDecl {
    /// Import path, e.g. `Fir.Prelude`.
    pub path: Vec<Id>,
    // TODO: Imported thing list, renaming (`as`).
}

#[derive(Debug, Clone)]
pub struct TraitDecl {
    /// Trait name.
    pub name: L<Id>,

    /// Type parameters of the trait.
    pub params: Vec<L<Id>>,

    /// Methods of the trait.
    pub items: Vec<L<FunDecl>>,
}

/// Type parameter and predicates of an `impl` or function.
///
/// E.g. `[Iterator[coll, item], Debug[item]]`.
#[derive(Debug, Clone)]
pub struct Context {
    /// Type parameters, generated by the type checker.
    pub type_params: Vec<(Id, Kind)>,

    /// Predicates.
    pub preds: Vec<L<Type>>,
}

/// An `impl` block, implementing a trait for a type.
///
/// ```ignore
/// impl[ToStr[a]] ToStr[Vec[a]]:
///   toStr(self): Str = ...
///
/// impl Iterator[VecIter[a], a]:
///   next(self): Option[a] = ...
/// ```
#[derive(Debug, Clone)]
pub struct ImplDecl {
    /// Predicates of the `impl` block.
    ///
    /// In the example: `[ToStr[a]]`.
    pub context: Context,

    /// The trait name.
    ///
    /// In the example: `ToStr`.
    pub trait_: L<Id>,

    /// Type parameters of the trait.
    ///
    /// In the example: `[Vec[a]]`.
    pub tys: Vec<L<Type>>,

    /// Method implementations.
    pub items: Vec<L<FunDecl>>,
}

impl Type {
    /// Substitute star-kinded `ty` for `var` in `self`.
    pub fn subst_id(&self, var: &Id, ty: &Type) -> Type {
        self.subst_ids(&[(var.clone(), ty.clone())].into_iter().collect())
    }

    pub fn subst_ids(&self, substs: &Map<Id, Type>) -> Type {
        match self {
            Type::Named(NamedType { name, args }) => Type::Named(NamedType {
                name: match substs.get(name) {
                    Some(ty) => {
                        assert!(args.is_empty());
                        return ty.clone();
                    }
                    None => name.clone(),
                },
                args: args
                    .iter()
                    .map(|L { loc, node: ty_ }| L {
                        loc: loc.clone(),
                        node: ty_.subst_ids(substs),
                    })
                    .collect(),
            }),

            Type::Var(var_) => match substs.get(var_) {
                Some(ty) => ty.clone(),
                None => Type::Var(var_.clone()),
            },

            Type::Record { fields, extension } => Type::Record {
                fields: fields
                    .iter()
                    .map(|Named { name, node }| Named {
                        name: name.clone(),
                        node: node.subst_ids(substs),
                    })
                    .collect(),
                // NB. This does not substitute row types.
                extension: extension.clone(),
            },

            Type::Variant { alts, extension } => Type::Variant {
                alts: alts
                    .iter()
                    .map(|VariantAlt { con, fields }| VariantAlt {
                        con: con.clone(),
                        fields: fields
                            .iter()
                            .map(|Named { name, node }| Named {
                                name: name.clone(),
                                node: node.subst_ids(substs),
                            })
                            .collect(),
                    })
                    .collect(),
                // NB. This does not substitute row types.
                extension: extension.clone(),
            },

            Type::Fn(FnType {
                args,
                ret,
                exceptions,
            }) => Type::Fn(FnType {
                args: args
                    .iter()
                    .map(|arg| arg.map_as_ref(|arg| arg.subst_ids(substs)))
                    .collect(),
                ret: ret
                    .as_ref()
                    .map(|ret| ret.map_as_ref(|ret| Box::new(ret.subst_ids(substs)))),
                exceptions: exceptions
                    .as_ref()
                    .map(|exn| exn.map_as_ref(|exn| Box::new(exn.subst_ids(substs)))),
            }),
        }
    }

    pub fn as_named_type(&self) -> &NamedType {
        match self {
            Type::Named(named_type) => named_type,
            _ => panic!(),
        }
    }
}
