//! Numbering pass lowers monomorphic AST to eliminate type arguments. All function and consturctor
//! references are converted into indices by this pass.

use crate::collections::Map;
use crate::mono_ast::{self as mono, AssignOp, BinOp, Id, IntExpr, Named, UnOp, L};

use smol_str::SmolStr;

#[derive(Debug)]
pub struct LoweredPgm {
    funs: Vec<Fun>,
    cons: Vec<Con>,
    closures: Vec<Closure>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FunIdx(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ConIdx(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LocalIdx(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FieldIdx(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ClosureIdx(u32);

// For now we will monomorphise fully but allocate anything other than integeres, bools, and chars
// as boxes. We also don't need to distinguish pointers from other word-sized things as we don't
// have a garbage collection yet.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Repr {
    U8,
    U32,
    U64,
}

impl Repr {
    fn from_mono_ty(mono_ty: &mono::Type) -> Repr {
        match mono_ty {
            mono::Type::Named(mono::NamedType { name, args: _ }) => {
                match name.as_str() {
                    "I8" | "U8" => Repr::U8,
                    "I32" | "U32" => Repr::U32,
                    "I64" | "U64" => Repr::U64,
                    "Char" => Repr::U32,
                    "Bool" => Repr::U8,
                    _ => Repr::U64, // box
                }
            }

            mono::Type::Record { .. } | mono::Type::Variant { .. } | mono::Type::Fn(_) => Repr::U64,
        }
    }
}

#[derive(Debug)]
pub struct Ty {
    pub mono_ty: mono::Type, // for debugging
    pub repr: Repr,
}

#[derive(Debug)]
pub enum Fun {
    Bultin(BuiltinFunDecl),
    Source(SourceFunDecl),
}

#[derive(Debug)]
pub enum BuiltinFunDecl {}

#[derive(Debug)]
pub struct SourceFunDecl {
    pub name: Id,                 // for debugging
    pub idx: FunIdx,              // for debugging
    pub ty_args: Vec<mono::Type>, // for debugging
    pub params: Vec<Ty>,
    pub return_ty: Ty,
    pub exceptions: Ty,
    pub body: Vec<L<Stmt>>,
}

#[derive(Debug)]
pub enum Con {
    Builtin(BuiltinConDecl),
    Source(SourceConDecl),
}

#[derive(Debug)]
pub enum BuiltinConDecl {
    ArrayU8,
    ArrayU32,
    ArrayU64,
    I8,
    U8,
    I32,
    U32,
}

#[derive(Debug)]
pub struct SourceConDecl {
    pub name: Id,                 // for debugging
    pub idx: ConIdx,              // for debugging
    pub ty_args: Vec<mono::Type>, // for debugging
    pub fields: ConFields,
}

#[derive(Debug)]
pub enum ConFields {
    Named(Vec<(Id, Ty)>),
    Unnamed(Vec<Ty>),
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Let(LetStmt),
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
    pub rhs: L<Expr>,
}

#[derive(Debug, Clone)]
pub struct AssignStmt {
    pub lhs: L<Expr>,
    pub rhs: L<Expr>,
    pub op: AssignOp,
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
    LocalVar(LocalIdx),             // a local variable
    TopVar(FunIdx),                 // a top-level function reference
    Constr(ConIdx),                 // a product constructor
    FieldSelect(FieldSelectExpr),   // <expr>.<id> (TODO: This could be lowered as function calls)
    MethodSelect(MethodSelectExpr), // <id>.<id>, with an object captured as receiver
    AssocFnSelect(FunIdx),          // <id>.<id>
    Call(CallExpr),
    Int(IntExpr),
    String(Vec<StringPart>),
    Char(char),
    Self_,
    BoolAnd(Box<L<Expr>>, Box<L<Expr>>),
    BoolOr(Box<L<Expr>>, Box<L<Expr>>),
    Record(Vec<Named<L<Expr>>>),
    Variant(VariantExpr),
    Return(Box<L<Expr>>),
    Match(MatchExpr),
    If(IfExpr),
    Fn(ClosureIdx),
}

#[derive(Debug, Clone)]
pub struct FieldSelectExpr {
    pub object: Box<L<Expr>>,
    pub field: FieldIdx,
}

#[derive(Debug, Clone)]
pub struct MethodSelectExpr {
    pub object: Box<L<Expr>>,
    pub fun_idx: FunIdx,
}

#[derive(Debug, Clone)]
pub struct CallExpr {
    pub fun: Box<L<Expr>>,
    pub args: Vec<L<Expr>>,
}

#[derive(Debug, Clone)]
pub struct BinOpExpr {
    pub left: Box<L<Expr>>,
    pub right: Box<L<Expr>>,
    pub op: BinOp, // only boolean and and or, so this is monomorphic
}

#[derive(Debug, Clone)]
pub struct UnOpExpr {
    pub op: UnOp, // only boolean not, so this is monomorphic
    pub expr: Box<L<Expr>>,
}

#[derive(Debug, Clone)]
pub struct VariantExpr {
    pub con_idx: ConIdx,
    pub args: Vec<Named<L<Expr>>>,
}

#[derive(Debug, Clone)]
pub enum StringPart {
    Str(String),
    Expr(L<Expr>),
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
pub struct IfExpr {
    pub branches: Vec<(L<Expr>, Vec<L<Stmt>>)>,
    pub else_branch: Option<Vec<L<Stmt>>>,
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
    pub constr: ConIdx,
    pub fields: Vec<Named<L<Pat>>>,
}

#[derive(Debug, Clone)]
pub struct VariantPattern {
    pub constr: ConIdx,
    pub fields: Vec<Named<L<Pat>>>,
}

#[derive(Debug)]
pub struct Closure {
    pub fvs: Vec<(LocalIdx, u32)>,
    pub args: u32,
    pub body: Vec<L<Stmt>>,
}

////////////////////////////////////////////////////////////////////////////////////////////////////

pub fn lower(mono_pgm: &mono::MonoPgm) -> LoweredPgm {
    // Number all declarations first, then lower the program.
    let mut product_con_nums: Map<(Id, Vec<mono::Type>), ConIdx> = Default::default();
    let mut sum_con_nums: Map<(Id, Id, Vec<mono::Type>), ConIdx> = Default::default();
    let mut fun_nums: Map<(Id, Vec<mono::Type>), FunIdx> = Default::default();
    let mut assoc_fun_nums: Map<(Id, Id, Vec<mono::Type>), FunIdx> = Default::default();

    // Number type declarations.
    for (con_id, con_ty_map) in &mono_pgm.ty {
        for (con_ty_args, con_decl) in con_ty_map {
            match &con_decl.rhs {
                Some(mono::TypeDeclRhs::Sum(cons)) => {
                    for con in cons {
                        let key = (con_id.clone(), con.name.clone(), con_ty_args.clone());
                        let next_idx = ConIdx((sum_con_nums.len() + product_con_nums.len()) as u32);
                        sum_con_nums.entry(key).or_insert(next_idx);
                    }
                }

                Some(mono::TypeDeclRhs::Product(_)) | None => {
                    // No RHS means it's either an uninhabited type like Void or a primitive. We
                    // can't distinguish the two here, so we assume primitive and give a number to
                    // all types without a RHS.
                    let key = (con_id.clone(), con_ty_args.clone());
                    let next_idx = ConIdx((sum_con_nums.len() + product_con_nums.len()) as u32);
                    product_con_nums.entry(key).or_insert(next_idx);
                }
            }
        }
    }

    // Number top-level functions.
    for (fun_id, fun_ty_map) in &mono_pgm.funs {
        for (fun_ty_args, _fun_decl) in fun_ty_map {
            let key = (fun_id.clone(), fun_ty_args.clone());
            let next_idx = FunIdx((fun_nums.len() + assoc_fun_nums.len()) as u32);
            fun_nums.entry(key).or_insert(next_idx);
        }
    }

    // Number associated functions.
    for (fun_ty_id, assoc_fn_map) in &mono_pgm.associated {
        for (fun_id, fun_ty_map) in assoc_fn_map {
            for (fun_ty_args, _fun_decl) in fun_ty_map {
                let key = (fun_ty_id.clone(), fun_id.clone(), fun_ty_args.clone());
                let next_idx = FunIdx((fun_nums.len() + assoc_fun_nums.len()) as u32);
                assoc_fun_nums.entry(key).or_insert(next_idx);
            }
        }
    }

    let mut lowered_pgm = LoweredPgm {
        funs: vec![],
        cons: vec![],
        closures: vec![],
    };

    // Lower the program. Note that the iteration order here should be the same as above to add
    // right definitions to the right indices in the vectors.

    // Lower types.
    for (con_id, con_ty_map) in &mono_pgm.ty {
        for (con_ty_args, con_decl) in con_ty_map {
            match &con_decl.rhs {
                Some(rhs) => match rhs {
                    mono::TypeDeclRhs::Sum(cons) => {
                        for mono::ConstructorDecl { name, fields } in cons {
                            let idx = ConIdx(lowered_pgm.cons.len() as u32);
                            let name = SmolStr::new(&format!("{}.{}", con_id, name));
                            lowered_pgm.cons.push(lower_source_con(
                                idx,
                                &name,
                                con_ty_args,
                                fields,
                            ));
                        }
                    }

                    mono::TypeDeclRhs::Product(fields) => {
                        let idx = ConIdx(lowered_pgm.cons.len() as u32);
                        lowered_pgm
                            .cons
                            .push(lower_source_con(idx, con_id, con_ty_args, fields));
                    }
                },

                None => match con_id.as_str() {
                    "Array" => {
                        assert_eq!(con_ty_args.len(), 1);
                        let elem_repr = Repr::from_mono_ty(&con_ty_args[0]);
                        let array_con = match elem_repr {
                            Repr::U8 => BuiltinConDecl::ArrayU8,
                            Repr::U32 => BuiltinConDecl::ArrayU32,
                            Repr::U64 => BuiltinConDecl::ArrayU64,
                        };
                        lowered_pgm.cons.push(Con::Builtin(array_con));
                    }

                    "I8" => lowered_pgm.cons.push(Con::Builtin(BuiltinConDecl::I8)),
                    "U8" => lowered_pgm.cons.push(Con::Builtin(BuiltinConDecl::U8)),
                    "I32" => lowered_pgm.cons.push(Con::Builtin(BuiltinConDecl::I32)),
                    "U32" => lowered_pgm.cons.push(Con::Builtin(BuiltinConDecl::U32)),

                    "Void" => {
                        // Lower as unit as we can't express empty types in the lowered
                        // representation.
                        // TODO: Could we just skip this?
                        // NOTE: This needs to be in sync with the numbering loop above.
                        let idx = ConIdx(lowered_pgm.cons.len() as u32);
                        lowered_pgm.cons.push(Con::Source(SourceConDecl {
                            name: SmolStr::new_static("Void"),
                            idx,
                            ty_args: vec![],
                            fields: ConFields::Unnamed(vec![]),
                        }))
                    }

                    other => panic!("Unknown built-in type: {}", other),
                },
            }
        }
    }

    // Lower top-level functions.
    for (fun_id, fun_ty_map) in &mono_pgm.funs {
        for (fun_ty_args, fun_decl) in fun_ty_map {
            todo!()
        }
    }

    // Number associated functions.
    for (fun_id, fun_ty_map) in &mono_pgm.funs {
        for (fun_ty_args, fun_decl) in fun_ty_map {
            todo!()
        }
    }

    lowered_pgm
}

fn lower_source_con(
    idx: ConIdx,
    con_id: &SmolStr,
    con_ty_args: &[mono::Type],
    fields: &mono::ConstructorFields,
) -> Con {
    Con::Source(SourceConDecl {
        name: con_id.clone(),
        idx,
        ty_args: con_ty_args.to_vec(),
        fields: match fields {
            mono::ConstructorFields::Empty => ConFields::Unnamed(vec![]),

            mono::ConstructorFields::Named(fields) => ConFields::Named(
                fields
                    .iter()
                    .map(|(name, field_ty)| {
                        (
                            name.clone(),
                            Ty {
                                mono_ty: field_ty.clone(),
                                repr: Repr::from_mono_ty(field_ty),
                            },
                        )
                    })
                    .collect(),
            ),

            mono::ConstructorFields::Unnamed(fields) => ConFields::Unnamed(
                fields
                    .iter()
                    .map(|field_ty| Ty {
                        mono_ty: field_ty.clone(),
                        repr: Repr::from_mono_ty(field_ty),
                    })
                    .collect(),
            ),
        },
    })
}
