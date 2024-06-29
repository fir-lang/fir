use crate::interpolation::StringPart;

use std::rc::Rc;

use smol_str::SmolStr;

/// Things with location information.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct L<T> {
    pub loc: Loc,
    pub thing: T,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Loc {
    pub module: Rc<str>,
    pub line_start: u16,
    pub col_start: u16,
    pub byte_offset_start: u32,
    pub line_end: u16,
    pub col_end: u16,
    pub byte_offset_end: u32,
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

impl<T> L<T> {
    pub fn new(module: &Rc<str>, start: lexgen_util::Loc, end: lexgen_util::Loc, thing: T) -> Self {
        L {
            loc: Loc::from_lexgen(module, start, end),
            thing,
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
}

/// A type declaration: `type Vec[T] = ...`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeDecl {
    /// The type name, e.g. `Vec`.
    pub name: SmolStr,

    /// Type parameters, e.g. `[T]`.
    #[allow(unused)]
    pub type_params: Vec<SmolStr>,

    /// Constructors of the type.
    pub rhs: TypeDeclRhs,
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
    Named(NamedType),
    Record(Vec<Named<Type>>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NamedType {
    #[allow(unused)]
    pub name: SmolStr,
    pub args: Vec<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Named<T> {
    pub name: Option<SmolStr>,
    pub thing: T,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunDecl {
    /// For associated functions, name of the type the function belongs.
    pub type_name: Option<SmolStr>,

    /// Name of the function.
    pub name: SmolStr,

    // TODO: Do we need to specify kinds?
    #[allow(unused)]
    pub type_params: Vec<SmolStr>,

    // Predicates in a separate list.
    #[allow(unused)]
    pub predicates: Vec<Type>,

    /// Whether the function has a `self` parameter.
    pub self_: bool,

    pub params: Vec<(SmolStr, Type)>,

    pub return_ty: Option<Type>,

    pub body: L<Vec<L<Stmt>>>,
}

impl FunDecl {
    pub fn num_params(&self) -> u32 {
        self.params.len() as u32 + if self.self_ { 1 } else { 0 }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    Let(LetStatement),
    // LetFn(FunDecl),
    Assign(AssignStatement),
    Expr(L<Expr>),
    For(ForStatement),
    While(WhileStatement),
}

/// A let statement: `let x: T = expr`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LetStatement {
    pub lhs: L<Pat>,
    pub ty: Option<Type>,
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

    Str(String),

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
pub struct AssignStatement {
    pub lhs: L<Expr>,
    pub rhs: L<Expr>,
    pub op: AssignOp,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignOp {
    Eq,
    PlusEq,
    MinusEq,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ForStatement {
    pub var: SmolStr,
    pub ty: Option<Type>,
    pub expr: L<Expr>,
    pub body: Vec<L<Stmt>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WhileStatement {
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

    Int(i32),

    String(Vec<StringPart>),

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
