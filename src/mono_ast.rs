pub mod printer;

pub use crate::ast::{AssignOp, BinOp, Id, IntExpr, L, Loc, Named, UnOp};
use crate::collections::*;
use crate::token::IntKind;

#[derive(Debug, Default)]
pub struct MonoPgm {
    // Fun name -> type args -> decl
    pub funs: Map<Id, Map<Vec<Type>, FunDecl>>,

    // Type name -> method name -> type args -> decl
    // For now, this also includes trait and normal methods. This means we don't allow having an
    // associated function and a method with the same name on the same type with same type
    // arguments.
    pub associated: Map<Id, Map<Id, Map<Vec<Type>, FunDecl>>>,

    // Type name -> type args -> decl
    pub ty: Map<Id, Map<Vec<Type>, TypeDecl>>,
}

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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Named(NamedType),

    Record { fields: Vec<Named<Type>> },

    // NB. Alts should be sorted by label.
    Variant { alts: Vec<NamedType> },

    Fn(FnType),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NamedType {
    pub name: Id,
    pub args: Vec<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FnType {
    pub args: FunArgs,
    pub ret: Option<L<Box<Type>>>,
    pub exceptions: Option<L<Box<Type>>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FunArgs {
    Positional(Vec<Type>),
    Named(TreeMap<Id, Type>),
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

#[derive(Debug, Clone)]
pub enum Stmt {
    Let(LetStmt),
    // LetFn(FunDecl),
    Assign(AssignStmt),
    Expr(L<Expr>),
    For(ForStmt),
    While(WhileStmt),
    Break { label: Option<Id>, level: u32 },
    Continue { label: Option<Id>, level: u32 },
}

#[derive(Debug, Clone)]
pub struct LetStmt {
    pub lhs: L<Pat>,
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
    Var(VarPat),
    Constr(ConstrPattern),
    Record(RecordPattern),
    Ignore,
    Str(String),
    Char(char),
    Or(Box<L<Pat>>, Box<L<Pat>>),
}

#[derive(Debug, Clone)]
pub struct VarPat {
    pub var: Id,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub struct ConstrPattern {
    pub constr: Constructor,

    // Note: this does not need to bind or match all fields!
    pub fields: Vec<Named<L<Pat>>>,
}

#[derive(Debug, Clone)]
pub struct Constructor {
    pub ty: Id,
    pub constr: Option<Id>,
    pub ty_args: Vec<Type>,
}

#[derive(Debug, Clone)]
pub struct RecordPattern {
    pub fields: Vec<Named<L<Pat>>>,
    pub ty: Type,
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

#[derive(Debug, Clone)]
pub struct ForStmt {
    pub pat: L<Pat>,
    pub expr: L<Expr>,
    pub body: Vec<L<Stmt>>,
    pub iter_ty: Type,
    pub item_ty: Type,
}

#[derive(Debug, Clone)]
pub struct WhileStmt {
    pub label: Option<Id>,
    pub cond: L<Expr>,
    pub body: Vec<L<Stmt>>,
}

#[derive(Debug, Clone)]
pub enum Expr {
    LocalVar(Id),                     // a local variable
    TopVar(VarExpr),                  // a top-level function reference
    ConstrSelect(Constructor),        // a product or sum constructor
    FieldSelect(FieldSelectExpr),     // <expr>.<id>
    MethodSelect(MethodSelectExpr),   // <id>.<id>, with an object captured as receiver
    AssocFnSelect(AssocFnSelectExpr), // <id>.<id>
    Call(CallExpr),
    Int(IntExpr),
    Str(Vec<StringPart>),
    Char(char),
    BinOp(BinOpExpr),
    UnOp(UnOpExpr),
    Record(Vec<Named<L<Expr>>>),
    Return(Box<L<Expr>>),
    Match(MatchExpr),
    If(IfExpr),
    Fn(FnExpr),
    Is(IsExpr),
    Do(Vec<L<Stmt>>),
    Variant(Box<L<Expr>>),
}

#[derive(Debug, Clone)]
pub struct VarExpr {
    pub id: Id,
    pub ty_args: Vec<Type>,
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
    pub ty_args: Vec<Type>,
}

#[derive(Debug, Clone)]
pub struct AssocFnSelectExpr {
    pub ty: Id,
    pub member: Id,
    pub ty_args: Vec<Type>,
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
pub struct FnExpr {
    pub sig: FunSig,
    pub body: Vec<L<Stmt>>,
}

#[derive(Debug, Clone)]
pub struct IsExpr {
    pub expr: Box<L<Expr>>,
    pub pat: L<Pat>,
}

#[derive(Debug, Clone)]
pub enum StringPart {
    Str(String),
    Expr(L<Expr>),
}
