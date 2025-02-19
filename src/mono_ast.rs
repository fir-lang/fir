use crate::ast::{self, Id, Loc, Named, L};
use crate::collections::*;
use crate::token::IntKind;

#[derive(Debug, Clone)]
pub struct TypeDecl {
    pub name: Id,
    pub rhs: Option<TypeDeclRhs>,
}

#[derive(Debug, Clone)]
pub enum TypeDeclRhs {
    Sum(Vec<ConstructorDecl>),
    Product(ConstructorFields),
}

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
    Named(Id),
    Record { fields: Vec<Named<Type>> },
    Variant { alts: Vec<VariantAlt> },
    Fn(FnType),
}

#[derive(Debug, Clone)]
pub struct VariantAlt {
    pub con: Id,
    pub fields: Vec<Named<Type>>,
}

#[derive(Debug, Clone)]
pub struct FnType {
    pub args: Vec<L<Type>>,
    pub ret: Option<L<Box<Type>>>,
    pub exceptions: Option<L<Box<Type>>>,
}

#[derive(Debug, Clone)]
pub struct FunSig {
    pub self_: SelfParam,
    pub params: Vec<(Id, L<Type>)>,
    pub return_ty: Option<L<Type>>,
    pub exceptions: Option<L<Type>>,
}

#[derive(Debug, Clone)]
pub enum SelfParam {
    No,
    Implicit,
    Explicit(L<Type>),
}

#[derive(Debug, Clone)]

pub struct FunDecl {
    pub parent_ty: Option<L<Id>>,
    pub name: L<Id>,
    pub sig: FunSig,
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
    Break { label: Option<Id>, level: u32 },
    Continue { label: Option<Id>, level: u32 },
}

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
    Var(Id),
    Constr(ConstrPattern),
    Variant(VariantPattern),
    Record(Vec<Named<L<Pat>>>),
    Ignore,
    Str(String),
    Char(char),
    StrPfx(String, Id),
    Or(Box<L<Pat>>, Box<L<Pat>>),
}

#[derive(Debug, Clone)]
pub struct ConstrPattern {
    pub constr: Constructor,
    pub fields: Vec<Named<L<Pat>>>,
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
    pub expr: L<Expr>,
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
    Var(VarExpr),
    Constr(ConstrExpr),               // a product constructor
    ConstrSelect(ConstrSelectExpr),   // <id>.<id>, a sum constructor
    FieldSelect(FieldSelectExpr),     // <expr>.<id> (TODO: This could be lowered as function calls)
    MethodSelect(MethodSelectExpr),   // <id>.<id>, with an object captured as receiver
    AssocFnSelect(AssocFnSelectExpr), // <id>.<id>
    Call(CallExpr),
    Int(IntExpr),
    String(Vec<StringPart>),
    Char(char),
    Self_,
    BinOp(BinOpExpr),
    UnOp(UnOpExpr),
    Record(Vec<Named<L<Expr>>>),
    Variant(VariantExpr),
    Return(Box<L<Expr>>),
    Match(MatchExpr),
    If(IfExpr),
    Fn(FnExpr),
}

#[derive(Debug, Clone)]
pub struct VarExpr {
    pub id: Id,
}

#[derive(Debug, Clone)]
pub struct ConstrExpr {
    pub id: Id,
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

#[derive(Debug, Clone)]
pub struct FieldSelectExpr {
    pub object: Box<L<Expr>>,
    pub field: Id,
}

#[derive(Debug, Clone)]
pub struct MethodSelectExpr {
    pub object: Box<L<Expr>>,
    pub method_ty_id: Id,
    pub method_id: Id,
}

#[derive(Debug, Clone)]
pub struct ConstrSelectExpr {
    pub ty: Id,
    pub constr: Id,
}

#[derive(Debug, Clone)]
pub struct AssocFnSelectExpr {
    pub ty: Id,
    pub member: Id,
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
    pub text: String,
    pub suffix: Option<IntKind>,
    pub radix: u32,
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

#[derive(Debug, Clone)]
pub enum StringPart {
    Str(String),
    Expr(L<Expr>),
}
