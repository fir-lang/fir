use lexgen_util::Loc;
use smol_str::SmolStr;

/// Things with location information.
#[derive(Debug, Clone)]
pub struct L<T> {
    pub start: Loc,
    #[allow(unused)]
    pub end: Loc,
    pub thing: T,
}

impl<T> L<T> {
    pub fn new(start: Loc, end: Loc, thing: T) -> Self {
        L { start, end, thing }
    }
}

/// A top-level declaration.
#[derive(Debug, Clone)]
pub enum TopDecl {
    /// A type declaration: `type T = ...`.
    Type(L<TypeDecl>),

    /// A function declaration: `fn f(...) = ...`.
    Fun(L<FunDecl>),
}

/// A type declaration: `type Vec[T] = ...`.
#[derive(Debug, Clone)]
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
    pub name: SmolStr,
    pub fields: ConstructorFields,
}

#[derive(Debug, Clone)]
pub enum ConstructorFields {
    Empty,
    Named(Vec<(SmolStr, Type)>),
    Unnamed(Vec<Type>),
}

#[derive(Debug, Clone)]
pub enum Type {
    Named(NamedType),
    Record(Vec<Named<Type>>),
}

#[derive(Debug, Clone)]
pub struct NamedType {
    #[allow(unused)]
    pub name: SmolStr,
    pub args: Vec<Type>,
}

#[derive(Debug, Clone)]
pub struct Named<T> {
    pub name: Option<SmolStr>,
    pub thing: T,
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub enum Stmt {
    Let(LetStatement),
    // LetFn(FunDecl),
    Match(MatchStatement),
    If(IfStatement),
    Assign(AssignStatement),
    Expr(L<Expr>),
    // For(ForStatement),
    While(WhileStatement),
    Return(L<Expr>),
}

/// A let statement: `let x: T = expr`.
#[derive(Debug, Clone)]
pub struct LetStatement {
    // For now, left-hand sides are just variables.
    pub lhs: SmolStr,

    pub ty: Option<Type>,

    pub rhs: L<Expr>,
}

#[derive(Debug, Clone)]
pub struct MatchStatement {
    pub scrutinee: L<Expr>,
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
    Var(SmolStr),

    /// Matches a constructor.
    Constr(ConstrPattern),

    Record(Vec<Named<Box<L<Pat>>>>),

    /// Underscore, aka. wildcard.
    Ignore,
    // TODO: Add literals
}

#[derive(Debug, Clone)]
pub struct ConstrPattern {
    pub constr: Constructor,
    pub fields: Vec<Named<Box<L<Pat>>>>,
}

#[derive(Debug, Clone)]
pub struct Constructor {
    pub type_: SmolStr,
    pub constr: Option<SmolStr>,
}

#[derive(Debug, Clone)]
pub struct IfStatement {
    // At least one element
    pub branches: Vec<(L<Expr>, Vec<L<Stmt>>)>,
    pub else_branch: Option<Vec<L<Stmt>>>,
}

#[derive(Debug, Clone)]
pub struct AssignStatement {
    pub lhs: L<Expr>,
    pub rhs: L<Expr>,
    pub op: AssignOp,
}

#[derive(Debug, Clone)]
pub enum AssignOp {
    Eq,
    PlusEq,
    MinusEq,
}

// #[derive(Debug, Clone)]
// pub struct ForStatement {
//     pub var: SmolStr,
//     pub ty: Option<Type>,
//     pub expr: L<Expr>,
//     pub body: Vec<Statement>,
// }

#[derive(Debug, Clone)]
pub struct WhileStatement {
    pub cond: L<Expr>,
    pub body: Vec<L<Stmt>>,
}

#[derive(Debug, Clone)]
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
    // Range(RangeExpr),
    Int(i32),

    String(String),

    Self_,

    BinOp(BinOpExpr),

    UnOp(UnOpExpr),

    ArrayIndex(ArrayIndexExpr),

    Record(Vec<Named<Box<L<Expr>>>>),
}

#[derive(Debug, Clone)]
pub struct CallExpr {
    pub fun: Box<L<Expr>>,
    pub args: Vec<CallArg>,
}

#[derive(Debug, Clone)]
pub struct CallArg {
    pub name: Option<SmolStr>,
    pub expr: L<Expr>,
}

#[derive(Debug, Clone)]
pub struct FieldSelectExpr {
    pub object: Box<L<Expr>>,
    pub field: SmolStr,
}

#[derive(Debug, Clone)]
pub struct ConstrSelectExpr {
    pub ty: SmolStr,
    pub constr: SmolStr,
}

// #[derive(Debug, Clone)]
// pub struct RangeExpr {
//     pub from: Box<L<Expr>>,
//     pub to: Box<L<Expr>>,
//     pub inclusive: bool,
// }

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
pub struct ArrayIndexExpr {
    pub array: Box<L<Expr>>,
    pub index: Box<L<Expr>>,
}

#[derive(Debug, Clone)]
pub enum BinOp {
    Add,
    Subtract,
    Equal,
    NotEqual,
    Multiply,
    Gt,
    And,
    Or,
}

#[derive(Debug, Clone)]
pub enum UnOp {
    Not,
}
