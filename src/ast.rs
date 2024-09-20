#![allow(clippy::enum_variant_names)]

mod printer;

use crate::interpolation::StringPart;

use std::rc::Rc;

use smol_str::SmolStr;

pub type Id = SmolStr;

/// Things with location information.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct L<T> {
    pub loc: Loc,
    pub node: T,
}

#[derive(Debug, Clone, PartialEq, Eq)]
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
#[derive(Debug, Clone, PartialEq, Eq)]
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
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeDecl {
    /// The type name, e.g. `Vec`.
    pub name: Id,

    /// Type parameters, e.g. `[T]`.
    pub type_params: Vec<Id>,

    /// Constructors of the type.
    pub rhs: Option<TypeDeclRhs>,
}

/// Constructors of a type declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeDeclRhs {
    /// A sum type, with more than one constructor.
    Sum(Vec<ConstructorDecl>),

    /// A product type uses the type name as the constructor and only has fields.
    Product(ConstructorFields),
}

/// A sum type constructor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorDecl {
    pub name: Id,
    pub fields: ConstructorFields,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstructorFields {
    Empty,
    Named(Vec<(Id, Type)>),
    Unnamed(Vec<Type>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    /// A type constructor, potentially applied some number of arguments. E.g. `I32`, `Vec[T]`.
    Named(NamedType),

    /// An anonymous record type, e.g. `{x: I32, y: I32}`.
    Record(Vec<Named<Type>>),
}

/// A named type, e.g. `I32`, `Vec[I32]`, `Iterator[Item = A]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NamedType {
    /// Name of the type constructor, e.g. `I32`, `Vec`, `Iterator`.
    pub name: Id,

    /// Arguments and associated types of the tyep constructor. Examples:
    ///
    /// - In `I32`, `[]`.
    /// - In `Vec[I32]`, `[(None, I32)]`.
    /// - In `Iterator[Item = A]`, `[(Some(Item), A)]`.
    pub args: Vec<L<(Option<Id>, L<Type>)>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Named<T> {
    pub name: Option<Id>,
    pub node: T,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssocType {
    /// In `Self.Item`, `Self`.
    pub ty: Box<L<Type>>,

    /// In `Self.Item`, `Item`.
    pub assoc_ty: Id,
}

/// Type signature part of a function declaration, including name, type parameters, parameters,
/// return type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunSig {
    /// Name of the function, e.g. in `fn f()` this is `f`.
    pub name: L<Id>,

    /// Type parameters of the function, e.g. in `fn id[T: Debug](a: T)` this is `[T: Debug]`.
    ///
    /// The bound can refer to assocaited types, e.g. `[A, I: Iterator[Item = A]]`.
    pub type_params: Context,

    /// Whether the function has a `self` parameter.
    pub self_: bool,

    /// Parameters of the function.
    pub params: Vec<(Id, L<Type>)>,

    /// Optional return type.
    pub return_ty: Option<L<Type>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunDecl {
    pub sig: FunSig,
    pub body: Option<L<Vec<L<Stmt>>>>,
}

impl FunDecl {
    pub fn num_params(&self) -> u32 {
        self.sig.params.len() as u32 + if self.sig.self_ { 1 } else { 0 }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    Let(LetStmt),
    // LetFn(FunDecl),
    Assign(AssignStmt),
    Expr(L<Expr>),
    For(ForStmt),
    While(WhileStmt),
}

/// A let statement: `let x: T = expr`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LetStmt {
    pub lhs: L<Pat>,
    pub ty: Option<L<Type>>,
    pub rhs: L<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatchExpr {
    pub scrutinee: Box<L<Expr>>,
    pub alts: Vec<Alt>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Alt {
    pub pattern: L<Pat>,
    pub guard: Option<L<Expr>>,
    pub rhs: Vec<L<Stmt>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pat {
    /// Matches anything, binds it to variable.
    Var(Id),

    /// Matches a constructor.
    Constr(ConstrPattern),

    Record(Vec<Named<Box<L<Pat>>>>),

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstrPattern {
    pub constr: Constructor,
    pub fields: Vec<Named<Box<L<Pat>>>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constructor {
    pub type_: Id,
    pub constr: Option<Id>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IfExpr {
    // At least one element
    pub branches: Vec<(L<Expr>, Vec<L<Stmt>>)>,
    pub else_branch: Option<Vec<L<Stmt>>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ForStmt {
    pub var: Id,
    pub ty: Option<Type>,
    pub expr: L<Expr>,
    pub body: Vec<L<Stmt>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WhileStmt {
    pub cond: L<Expr>,
    pub body: Vec<L<Stmt>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    /// A variable: `x`.
    Var(Id),

    /// A constructor: `Vec`, `Bool`, `I32`.
    Constr(Id),

    /// A field, method, or associated function selection: `<expr>.a`.
    ///
    /// Selection type depends on `<expr>`:
    ///
    /// - `UpperVar`: select associated function or method.
    /// - Any other expression: select field or method.
    FieldSelect(FieldSelectExpr),

    /// A constructor selection: `Option.None`.
    ConstrSelect(ConstrSelectExpr),

    /// A function call: `f(a)`.
    Call(CallExpr),

    /// A range expression: `x .. y`.
    Range(RangeExpr),

    Int(IntExpr),

    String(Vec<StringPart>),

    Char(char),

    Self_,

    BinOp(BinOpExpr),

    UnOp(UnOpExpr),

    ArrayIndex(ArrayIndexExpr),

    Record(Vec<Named<Box<L<Expr>>>>),

    Return(Box<L<Expr>>),

    Match(MatchExpr),

    If(IfExpr),

    /// Instantiation of a polymorphic function.
    ///
    /// These nodes are introduced by the type checker as it instantiates polymorphic functions.
    ///
    /// Monomorphisation then replaces these nodes with references to monomorphised functions.
    Instantiation(Path, Vec<crate::type_checker::Ty>),
}

/// Path to a polymorphic item.
// TODO: Find a better name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Path {
    /// Path to a top-level function.
    TopLevel { fun_id: Id },

    /// Path to a constructor, e.g. `Option.Some`.
    Constructor { ty_id: Id, constr_id: Id },

    /// Path to an associated function or method, e.g. `Vec.len` (method), `Vec.withCapacity`
    /// (associated function).
    AssociatedFn { ty_id: Id, fun_id: Id },

    /// Path to a method, e.g. `<expr>.a` where `a` is a method.
    Method {
        receiver: Box<Expr>,
        receiver_ty: crate::type_checker::Ty,
        method_id: Id,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallExpr {
    pub fun: Box<L<Expr>>,
    pub args: Vec<CallArg>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallArg {
    pub name: Option<Id>,
    pub expr: L<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldSelectExpr {
    pub object: Box<L<Expr>>,
    pub field: Id,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstrSelectExpr {
    pub ty: Id,
    pub constr: Id,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RangeExpr {
    pub from: Box<L<Expr>>,
    pub to: Box<L<Expr>>,
    pub inclusive: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinOpExpr {
    pub left: Box<L<Expr>>,
    pub right: Box<L<Expr>>,
    pub op: BinOp,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnOpExpr {
    pub op: UnOp,
    pub expr: Box<L<Expr>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArrayIndexExpr {
    pub array: Box<L<Expr>>,
    pub index: Box<L<Expr>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IntExpr {
    I8(i8),
    U8(u8),
    I32(i32),
    U32(u32),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Subtract,
    Equal,
    NotEqual,
    Multiply,
    Lt,
    Gt,
    LtEq,
    GtEq,
    And,
    Or,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnOp {
    Not,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportDecl {
    /// Import path, e.g. `Fir.Prelude`.
    pub path: Vec<Id>,
    // TODO: Imported thing list, renaming (`as`).
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraitDecl {
    /// Trait name.
    pub name: L<Id>,

    /// Type parameter of the trait, with bounds.
    pub ty: L<(Id, Vec<L<Type>>)>,

    pub items: Vec<L<TraitDeclItem>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TraitDeclItem {
    /// An associated type, e.g. `type Item`.
    AssocTy(Id),

    /// A method, potentially with a body (default implementation).
    Fun(FunDecl),
}

/// Type parameters of a function or `impl` block.
///
/// E.g. `[A, I: Iterator[Item = A]]` is represented as `[(A, []), (I, [Item = A])]`.
pub type Context = Vec<L<(L<Id>, Vec<L<Type>>)>>;

/// An `impl` block, implementing associated functions or methods for a type, or a trait. Examples:
///
/// ```ignore
/// impl[A] Vec[A]:
///     # An associated function.
///     fn withCapacity(cap: U32): Vec[A] = ...
///
///     # A method.
///     fn push(self, elem: A) = ...
///
/// impl[A: ToStr] ToStr for Vec[A]:
///   fn toStr(self): Str = ...
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImplDecl {
    /// Type parameters of the type being implemented, with bounds.
    ///
    /// In the first example, this is `[A]`. In the second example: `[A: ToStr]`.
    pub context: Context,

    /// If the `impl` block is for a trait, the trait name.
    ///
    /// In the first example this is `None`. In the second this is `Some(ToStr)`.
    pub trait_: Option<L<Id>>,

    /// The implementing type.
    ///
    /// In both of the examples this is `Vec[A]`.
    pub ty: L<Type>,

    /// Functions, methods, and associated types.
    pub items: Vec<L<ImplDeclItem>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImplDeclItem {
    /// An associated type definition, e.g. `type Item = T`.
    AssocTy(AssocTyDecl),

    /// A function definition.
    Fun(FunDecl),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssocTyDecl {
    pub name: Id,
    pub ty: L<Type>,
}

impl Type {
    pub fn subst_var(&self, var: &Id, ty: &Type) -> Type {
        match ty {
            Type::Named(NamedType { name, args }) => {
                if name == var {
                    assert!(args.is_empty());
                    ty.clone()
                } else {
                    Type::Named(NamedType {
                        name: name.clone(),
                        args: args
                            .iter()
                            .map(
                                |L {
                                     loc,
                                     node: (name, ty_),
                                 }| L {
                                    loc: loc.clone(),
                                    node: (
                                        name.clone(),
                                        ty_.map_as_ref(|ty__| ty__.subst_var(var, ty)),
                                    ),
                                },
                            )
                            .collect(),
                    })
                }
            }

            Type::Record(fields) => Type::Record(
                fields
                    .iter()
                    .map(|Named { name, node }| Named {
                        name: name.clone(),
                        node: node.subst_var(var, ty),
                    })
                    .collect(),
            ),
        }
    }
}
