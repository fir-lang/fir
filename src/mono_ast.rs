/*
We could add more information to funs and cons for debugging, i.e. original fun/type location, mono
type arguments.
*/

use crate::ast::{self, Id};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ConIdx(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FunIdx(u32);

#[derive(Debug)]
pub struct MonoPgm {
    /// Indexed by `ConIdx`.
    cons: Vec<Con>,

    /// Indexed by `FunIdx`.
    funs: Vec<Fun>,
}

#[derive(Debug, Clone)]
pub struct Type {
    pub name: Id, // for debugging
    pub cons: Vec<Con>,
}

#[derive(Debug, Clone)]
pub struct Con {
    pub name: Id, // for debugging
    pub fields: Vec<(Option<Id>, Type)>,
}

#[derive(Debug, Clone)]
pub struct Fun {
    pub name: Id, // for debugging
    pub args: Vec<(Id, Type)>,
    pub body: Option<Vec<Stmt>>,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Let {
        lhs: Pat,
        rhs: Expr,
    },

    Assign {
        lhs: Expr,
        rhs: Expr,
        op: ast::AssignOp,
    },

    Expr(Expr),

    For {
        label: Option<Id>,
        pat: Pat,
        expr: Expr,
        body: Vec<Stmt>,
    },

    While {
        label: Option<Id>,
        cond: Expr,
        body: Vec<Stmt>,
    },

    WhileLet {
        label: Option<Id>,
        cond: Expr,
        body: Vec<Stmt>,
    },

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

#[derive(Debug, Clone)]
pub enum Expr {
    Var(Id),

    Con(ConIdx),

    FieldSelect {
        expr: Box<Expr>,
        field: Id,
    },

    MethodSelect {
        object: Box<Expr>,
        fun: FunIdx,
    },

    Call {
        fun: Box<Expr>,
        args: Vec<(Option<Id>, Expr)>,
    },

    Int(u64),

    String(Vec<StringPart>),

    Char(char),

    BinOp {
        left: Box<Expr>,
        right: Box<Expr>,
        op: ast::BinOp,
    },

    UnOp {
        expr: Box<Expr>,
        op: ast::UnOp,
    },

    Record {
        fields: Vec<(Option<Id>, Expr)>,
    },

    Variant {
        id: Id,
        fields: Vec<(Option<Id>, Expr)>,
    },

    Return(Box<Expr>),

    Match {
        scrutinee: Box<Expr>,
        alt: Vec<Alt>,
    },

    If {
        branches: Vec<(Expr, Vec<Stmt>)>,
        else_branch: Option<Vec<Stmt>>,
    },

    Fn {
        args: Vec<(Id, Type)>,
        body: Vec<Stmt>,
    },
}

#[derive(Debug, Clone)]
pub struct Alt {
    pat: Pat,
    guard: Option<Expr>,
    rhs: Vec<Stmt>,
}

#[derive(Debug, Clone)]
pub enum Pat {
    Var(Id),
    Constr {
        idx: ConIdx,
        fields: Vec<(Option<Id>, Pat)>,
    },

    Variant {
        con: Id,
        fields: Vec<(Option<Id>, Pat)>,
    },

    Record {
        fields: Vec<(Option<Id>, Pat)>,
    },

    Ignore,

    Str(String),

    Char(char),

    StrPfx(String, Id),

    Or(Box<Pat>, Box<Pat>),
}

#[derive(Debug, Clone)]
pub enum StringPart {
    Str(String),
    Expr(Expr),
}
