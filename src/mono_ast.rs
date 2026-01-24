pub mod printer;

pub use crate::ast::{BinOp, Id, IntExpr, L, Loc, Named};
use crate::collections::*;
use crate::token::IntKind;

#[derive(Debug, Default)]
pub struct MonoPgm {
    // Fun name -> type args -> decl
    pub funs: HashMap<Id, HashMap<Vec<Type>, FunDecl>>,

    // Type name -> method name -> type args -> decl
    // For now, this also includes trait and normal methods. This means we don't allow having an
    // associated function and a method with the same name on the same type with same type
    // arguments.
    pub associated: HashMap<Id, HashMap<Id, HashMap<Vec<Type>, FunDecl>>>,

    // Type name -> type args -> decl
    pub ty: HashMap<Id, HashMap<Vec<Type>, TypeDecl>>,
}

#[derive(Debug, Clone)]
pub struct TypeDecl {
    pub name: Id,
    pub rhs: Option<TypeDeclRhs>,
}

#[derive(Debug, Clone)]
pub enum TypeDeclRhs {
    Sum(Vec<ConDecl>),
    Product(ConFields),
}

#[derive(Debug, Clone)]
pub struct ConDecl {
    pub name: Id,
    pub fields: ConFields,
}

#[derive(Debug, Clone)]
pub enum ConFields {
    Empty,
    Named(OrdMap<Id, Type>),
    Unnamed(Vec<Type>),
}

// Note: `Type` is used in maps and sets and it *cannot* have `Loc`s in it to avoid duplicating
// types that come from different locations.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Type {
    Named(NamedType),

    Record {
        fields: OrdMap<Id, Type>,
    },

    Variant {
        // Keys should be the same as named type's type constructor.
        //
        // TODO: This was a map instead of set to avoid making `Type` `Ord` or `Hash`, but `Type` is
        // now all of those things, so we can now refactor this.
        alts: OrdMap<Id, NamedType>,
    },

    Fn(FnType),

    /// Type of expressions that don't generate a value. E.g. `continue`, `break`.
    Never,
}

impl Type {
    pub(crate) fn unit() -> Type {
        Type::Record {
            fields: Default::default(),
        }
    }

    pub(crate) fn empty() -> Type {
        Type::Variant {
            alts: Default::default(),
        }
    }

    pub(crate) fn bool() -> Type {
        Type::Named(NamedType {
            name: crate::SmolStr::new_static("Bool"),
            args: vec![],
        })
    }

    pub(crate) fn u32() -> Type {
        Type::Named(NamedType {
            name: crate::SmolStr::new_static("U32"),
            args: vec![],
        })
    }

    pub(crate) fn is_never(&self) -> bool {
        matches!(self, Type::Never)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NamedType {
    pub name: Id,
    pub args: Vec<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FnType {
    pub args: FunArgs,
    pub ret: Box<Type>,
    pub exn: Box<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FunArgs {
    Positional(Vec<Type>),
    Named(OrdMap<Id, Type>),
}

#[derive(Debug, Clone)]
pub struct FunSig {
    pub params: Vec<(Id, L<Type>)>,
    pub return_ty: Option<L<Type>>,
    pub exceptions: Option<L<Type>>,
}

impl FunSig {
    pub(crate) fn ty(&self) -> FnType {
        FnType {
            args: FunArgs::Positional(
                self.params
                    .iter()
                    .map(|(_param_name, param_ty)| param_ty.node.clone())
                    .collect(),
            ),
            ret: Box::new(
                self.return_ty
                    .as_ref()
                    .map(|ty| ty.node.clone())
                    .unwrap_or(Type::unit()),
            ),
            exn: Box::new(
                self.exceptions
                    .as_ref()
                    .map(|ty| ty.node.clone())
                    .unwrap_or(Type::empty()),
            ),
        }
    }
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
    Assign(AssignStmt),
    Expr(Expr),
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
    pub scrut: Box<L<Expr>>,
    pub alts: Vec<Alt>,
}

#[derive(Debug, Clone)]
pub struct Alt {
    pub pat: L<Pat>,
    pub guard: Option<L<Expr>>,
    pub rhs: Vec<L<Stmt>>,
}

#[derive(Debug, Clone)]
pub enum Pat {
    Var(VarPat),
    Con(ConPat),
    Ignore,
    Str(String),
    Char(char),
    Or(Box<L<Pat>>, Box<L<Pat>>),
    Record(RecordPat),
    Variant(VariantPat),
}

#[derive(Debug, Clone)]
pub struct VarPat {
    pub var: Id,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub struct ConPat {
    pub con: Con,

    // Note: this does not need to bind or match all fields!
    pub fields: Vec<Named<L<Pat>>>,
}

#[derive(Debug, Clone)]
pub struct Con {
    pub ty: Id,
    pub con: Option<Id>,
    pub ty_args: Vec<Type>,
}

#[derive(Debug, Clone)]
pub struct RecordPat {
    pub fields: Vec<Named<L<Pat>>>,

    /// The record type.
    ///
    /// Note that the type can have more fields than `fields`. Those fields are ignored by the
    /// pattern.
    /// TODO: Maybe have a `ignore_rest` flag here as well?
    pub ty: OrdMap<Id, Type>,
}

#[derive(Debug, Clone)]
pub struct VariantPat {
    pub pat: Box<L<Pat>>,
    pub ty: OrdMap<Id, NamedType>, // the variant type
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
}

#[derive(Debug, Clone)]
pub struct WhileStmt {
    pub label: Option<Id>,
    pub cond: L<Expr>,
    pub body: Vec<L<Stmt>>,
}

#[derive(Debug, Clone)]
pub enum Expr {
    LocalVar(Id),               // a local variable
    TopVar(VarExpr),            // a top-level function reference
    ConSel(Con),                // a product or sum constructor
    FieldSel(FieldSelExpr),     // <expr>.<id>
    AssocFnSel(AssocFnSelExpr), // <id>.<id>
    Call(CallExpr),
    Int(IntExpr),
    Str(String),
    Char(char),
    BinOp(BinOpExpr),
    Return(Box<L<Expr>>),
    Match(MatchExpr),
    If(IfExpr),
    Fn(FnExpr),
    Is(IsExpr),
    Do(Vec<L<Stmt>>),
    Record(RecordExpr),
    Variant(VariantExpr),
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
pub struct FieldSelExpr {
    pub object: Box<L<Expr>>,
    pub field: Id,
}

#[derive(Debug, Clone)]
pub struct AssocFnSelExpr {
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
pub struct RecordExpr {
    pub fields: Vec<(Id, L<Expr>)>,
    pub ty: OrdMap<Id, Type>, // the record type
}

#[derive(Debug, Clone)]
pub struct VariantExpr {
    pub expr: Box<L<Expr>>,
    pub ty: OrdMap<Id, NamedType>, // the variant type
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
