#![allow(clippy::enum_variant_names)]

mod printer;

use crate::interpolation::StringPart;

use std::rc::Rc;

use smol_str::SmolStr;

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
    pub name: SmolStr,

    /// Type parameters, e.g. `[T]`.
    pub type_params: Vec<SmolStr>,

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
    pub name: SmolStr,
    pub fields: ConstructorFields,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstructorFields {
    Empty,
    Named(Vec<(SmolStr, Type)>),
    Unnamed(Vec<Type>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    /// A type constructor, potentially applied some number of arguments. E.g. `I32`, `Vec[T]`.
    Named(NamedType),

    /// An anonymous record type, e.g. `{x: I32, y: I32}`.
    Record(Vec<Named<Type>>),

    /// An associated type, e.g. `Self.Item`.
    AssocType(AssocType),
}

/// A named type, e.g. `I32`, `Vec[I32]`, `Iterator[Item = A]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NamedType {
    /// Name of the type constructor, e.g. `I32`, `Vec`, `Iterator`.
    pub name: SmolStr,

    /// Arguments and associated types of the tyep constructor. Examples:
    ///
    /// - In `I32`, `[]`.
    /// - In `Vec[I32]`, `[(None, I32)]`.
    /// - In `Iterator[Item = A]`, `[(Some(Item), A)]`.
    pub args: Vec<L<(Option<SmolStr>, L<Type>)>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Named<T> {
    pub name: Option<SmolStr>,
    pub node: T,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssocType {
    /// In `Self.Item`, `Self`.
    pub ty: Box<L<Type>>,

    /// In `Self.Item`, `Item`.
    pub assoc_ty: SmolStr,
}

/// Type signature part of a function declaration, including name, type parameters, parameters,
/// return type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunSig {
    /// Name of the function, e.g. in `fn f()` this is `f`.
    pub name: L<SmolStr>,

    /// Type parameters of the function, e.g. in `fn id[T: Debug](a: T)` this is `[T: Debug]`.
    ///
    /// The bound can refer to assocaited types, e.g. `[A, I: Iterator[Item = A]]`.
    pub type_params: Context,

    /// Whether the function has a `self` parameter.
    pub self_: bool,

    /// Parameters of the function.
    pub params: Vec<(SmolStr, L<Type>)>,

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
    Var(SmolStr),

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
    StrPfx(String, SmolStr),

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
    pub type_: SmolStr,
    pub constr: Option<SmolStr>,
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
    pub var: SmolStr,
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
    Var(SmolStr),

    /// An uppercase identifier: `X`.
    ///
    /// This can be a type or a constructor.
    UpperVar(SmolStr),

    /// A field selection: `x.a`.
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallExpr {
    pub fun: Box<L<Expr>>,
    pub args: Vec<CallArg>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallArg {
    pub name: Option<SmolStr>,
    pub expr: L<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldSelectExpr {
    pub object: Box<L<Expr>>,
    pub field: SmolStr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstrSelectExpr {
    pub ty: SmolStr,
    pub constr: SmolStr,
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
    pub path: Vec<SmolStr>,
    // TODO: Imported thing list, renaming (`as`).
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraitDecl {
    /// Trait name.
    pub name: L<SmolStr>,

    /// Type parameter of the trait, with bounds.
    pub ty: L<(SmolStr, Vec<L<Type>>)>,

    pub items: Vec<L<TraitDeclItem>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TraitDeclItem {
    /// An associated type, e.g. `type Item`.
    AssocTy(SmolStr),

    /// A method, potentially with a body (default implementation).
    Fun(FunDecl),
}

/// Type parameters of a function or `impl` block.
///
/// E.g. `[A, I: Iterator[Item = A]]` is represented as `[(A, []), (I, [Item = A])]`.
pub type Context = Vec<L<(L<SmolStr>, Vec<L<Type>>)>>;

/// An `impl` block, implementing associated methods for a type, or a trait.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImplDecl {
    /// Type parameters of the type being implemented, with bounds.
    pub context: Context,

    /// The type being implemented.
    ///
    /// This can be a trait (e.g. `Debug[Vec[T]]`) or a type (e.g. `Vec[T]`).
    pub ty: L<Type>,

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
    pub name: SmolStr,
    pub ty: L<Type>,
}

impl Type {
    pub fn subst_var(&self, var: &SmolStr, ty: &Type) -> Type {
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

            Type::AssocType(AssocType { ty: ty_, assoc_ty }) => Type::AssocType(AssocType {
                ty: Box::new(L {
                    loc: ty_.loc.clone(),
                    node: ty_.node.subst_var(var, ty),
                }),
                assoc_ty: assoc_ty.clone(),
            }),
        }
    }
}
