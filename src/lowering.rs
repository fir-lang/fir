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

impl Ty {
    fn from_mono_ty(ty: &mono::Type) -> Ty {
        Ty {
            mono_ty: ty.clone(),
            repr: Repr::from_mono_ty(ty),
        }
    }
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
    pub parent_ty: Option<L<Id>>, // for debugging
    pub name: L<Id>,              // for debugging
    pub idx: FunIdx,              // for debugging
    pub ty_args: Vec<mono::Type>, // for debugging
    pub locals: Vec<LocalInfo>,   // for debugging, indexed by `LocalIdx`
    pub params: Vec<Ty>,
    pub return_ty: Ty,
    pub exceptions: Ty,
    pub body: Vec<L<Stmt>>,
}

#[derive(Debug)]
pub struct LocalInfo {
    pub name: Id,
    pub ty: mono::Type,
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
    Self_, // TODO: Should this be a `LocalVar`?
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
    pub field: Id,
}

#[derive(Debug, Clone)]
pub struct MethodSelectExpr {
    pub object: Box<L<Expr>>,
    pub fun_idx: FunIdx,
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
    pub id: Id,
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
    Var(LocalIdx),
    Constr(ConstrPattern),
    Variant(VariantPattern),
    Record(Vec<Named<L<Pat>>>),
    Ignore,
    Str(String),
    Char(char),
    StrPfx(String, LocalIdx),
    Or(Box<L<Pat>>, Box<L<Pat>>),
}

#[derive(Debug, Clone)]
pub struct ConstrPattern {
    pub constr: ConIdx,
    pub fields: Vec<Named<L<Pat>>>,
}

#[derive(Debug, Clone)]
pub struct VariantPattern {
    pub constr: Id,
    pub fields: Vec<Named<L<Pat>>>,
}

#[derive(Debug)]
pub struct Closure {
    pub fvs: Vec<(LocalIdx, u32)>,
    pub args: u32,
    pub body: Vec<L<Stmt>>,
}

////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
struct Indices {
    product_con_nums: Map<Id, Map<Vec<mono::Type>, ConIdx>>,
    sum_con_nums: Map<Id, Map<Id, Map<Vec<mono::Type>, ConIdx>>>,
    fun_nums: Map<Id, Map<Vec<mono::Type>, FunIdx>>,
    assoc_fun_nums: Map<Id, Map<Id, Map<Vec<mono::Type>, FunIdx>>>,
    local_nums: Map<Id, LocalIdx>,
}

pub fn lower(mono_pgm: &mono::MonoPgm) -> LoweredPgm {
    // Number all declarations first, then lower the program.
    let mut product_con_nums: Map<Id, Map<Vec<mono::Type>, ConIdx>> = Default::default();
    let mut sum_con_nums: Map<Id, Map<Id, Map<Vec<mono::Type>, ConIdx>>> = Default::default();
    let mut fun_nums: Map<Id, Map<Vec<mono::Type>, FunIdx>> = Default::default();
    let mut assoc_fun_nums: Map<Id, Map<Id, Map<Vec<mono::Type>, FunIdx>>> = Default::default();

    // Number type declarations.
    for (con_id, con_ty_map) in &mono_pgm.ty {
        for (con_ty_args, con_decl) in con_ty_map {
            match &con_decl.rhs {
                Some(mono::TypeDeclRhs::Sum(cons)) => {
                    for con in cons {
                        let next_idx = ConIdx((sum_con_nums.len() + product_con_nums.len()) as u32);
                        sum_con_nums
                            .entry(con_id.clone())
                            .or_default()
                            .entry(con.name.clone())
                            .or_default()
                            .entry(con_ty_args.clone())
                            .or_insert(next_idx);
                    }
                }

                Some(mono::TypeDeclRhs::Product(_)) | None => {
                    // No RHS means it's either an uninhabited type like Void or a primitive. We
                    // can't distinguish the two here, so we assume primitive and give a number to
                    // all types without a RHS.
                    let next_idx = ConIdx((sum_con_nums.len() + product_con_nums.len()) as u32);
                    product_con_nums
                        .entry(con_id.clone())
                        .or_default()
                        .entry(con_ty_args.clone())
                        .or_insert(next_idx);
                }
            }
        }
    }

    // Number top-level functions.
    for (fun_id, fun_ty_map) in &mono_pgm.funs {
        for (fun_ty_args, _fun_decl) in fun_ty_map {
            let next_idx = FunIdx((fun_nums.len() + assoc_fun_nums.len()) as u32);
            fun_nums
                .entry(fun_id.clone())
                .or_default()
                .entry(fun_ty_args.clone())
                .or_insert(next_idx);
        }
    }

    // Number associated functions.
    for (fun_ty_id, assoc_fn_map) in &mono_pgm.associated {
        for (fun_id, fun_ty_map) in assoc_fn_map {
            for (fun_ty_args, _fun_decl) in fun_ty_map {
                let next_idx = FunIdx((fun_nums.len() + assoc_fun_nums.len()) as u32);
                assoc_fun_nums
                    .entry(fun_ty_id.clone())
                    .or_default()
                    .entry(fun_id.clone())
                    .or_default()
                    .entry(fun_ty_args.clone())
                    .or_insert(next_idx);
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

    let mut indices = Indices {
        product_con_nums,
        sum_con_nums,
        fun_nums,
        assoc_fun_nums,
        local_nums: Default::default(), // updated in each function
    };

    // Lower top-level functions.
    for (_fun_id, fun_ty_map) in &mono_pgm.funs {
        for (fun_ty_args, fun_decl) in fun_ty_map {
            let idx = FunIdx(lowered_pgm.funs.len() as u32);
            if fun_decl.body.is_some() {
                let source_fun = lower_source_fun(fun_decl, idx, fun_ty_args, &mut indices);
                lowered_pgm.funs.push(Fun::Source(source_fun));
            } else {
                // TODO: built-ins
            }
        }
    }

    // Number associated functions.
    for (_fun_id, fun_ty_map) in &mono_pgm.funs {
        for (fun_ty_args, fun_decl) in fun_ty_map {
            let idx = FunIdx(lowered_pgm.funs.len() as u32);
            if fun_decl.body.is_some() {
                let source_fun = lower_source_fun(fun_decl, idx, fun_ty_args, &mut indices);
                lowered_pgm.funs.push(Fun::Source(source_fun));
            } else {
                // TODO: built-ins
            }
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

fn lower_stmt(stmt: &mono::Stmt, indices: &mut Indices) -> Stmt {
    match stmt {
        mono::Stmt::Let(mono::LetStmt { lhs, rhs }) => Stmt::Let(LetStmt {
            lhs: lower_l_pat(lhs, indices),
            rhs: lower_l_expr(rhs, indices),
        }),

        mono::Stmt::Assign(mono::AssignStmt { lhs, rhs, op }) => Stmt::Assign(AssignStmt {
            lhs: lower_l_expr(lhs, indices),
            rhs: lower_l_expr(rhs, indices),
            op: *op,
        }),

        mono::Stmt::Expr(expr) => Stmt::Expr(lower_l_expr(expr, indices)),

        mono::Stmt::For(mono::ForStmt {
            label,
            pat,
            expr,
            body,
        }) => Stmt::For(ForStmt {
            label: label.clone(),
            pat: lower_l_pat(pat, indices),
            expr: lower_l_expr(expr, indices),
            body: body
                .iter()
                .map(|stmt| lower_l_stmt(stmt, indices))
                .collect(),
        }),

        mono::Stmt::While(mono::WhileStmt { label, cond, body }) => Stmt::While(WhileStmt {
            label: label.clone(),
            cond: lower_l_expr(cond, indices),
            body: body
                .iter()
                .map(|stmt| lower_l_stmt(stmt, indices))
                .collect(),
        }),

        mono::Stmt::WhileLet(mono::WhileLetStmt {
            label,
            pat,
            cond,
            body,
        }) => Stmt::WhileLet(WhileLetStmt {
            label: label.clone(),
            pat: lower_l_pat(pat, indices),
            cond: lower_l_expr(cond, indices),
            body: body
                .iter()
                .map(|stmt| lower_l_stmt(stmt, indices))
                .collect(),
        }),

        mono::Stmt::Break { label, level } => Stmt::Break {
            label: label.clone(),
            level: *level,
        },

        mono::Stmt::Continue { label, level } => Stmt::Continue {
            label: label.clone(),
            level: *level,
        },
    }
}

fn lower_l_stmt(stmt: &L<mono::Stmt>, indices: &mut Indices) -> L<Stmt> {
    stmt.map_as_ref(|stmt| lower_stmt(stmt, indices))
}

fn lower_expr(expr: &mono::Expr, indices: &mut Indices) -> Expr {
    match expr {
        mono::Expr::LocalVar(var) => Expr::LocalVar(*indices.local_nums.get(var).unwrap()),

        mono::Expr::TopVar(mono::VarExpr { id, ty_args }) => {
            Expr::TopVar(*indices.fun_nums.get(id).unwrap().get(ty_args).unwrap())
        }

        mono::Expr::Constr(mono::ConstrExpr { id, ty_args }) => Expr::Constr(
            *indices
                .product_con_nums
                .get(id)
                .unwrap()
                .get(ty_args)
                .unwrap(),
        ),

        mono::Expr::ConstrSelect(mono::ConstrSelectExpr {
            ty,
            constr,
            ty_args,
        }) => Expr::Constr(
            *indices
                .sum_con_nums
                .get(ty)
                .unwrap()
                .get(constr)
                .unwrap()
                .get(ty_args)
                .unwrap(),
        ),

        mono::Expr::FieldSelect(mono::FieldSelectExpr { object, field }) => {
            Expr::FieldSelect(FieldSelectExpr {
                object: lower_bl_expr(object, indices),
                field: field.clone(),
            })
        }

        mono::Expr::MethodSelect(mono::MethodSelectExpr {
            object,
            method_ty_id,
            method_id,
            ty_args,
        }) => {
            let fun_idx = *indices
                .assoc_fun_nums
                .get(method_ty_id)
                .unwrap()
                .get(method_id)
                .unwrap()
                .get(ty_args)
                .unwrap();

            Expr::MethodSelect(MethodSelectExpr {
                object: lower_bl_expr(object, indices),
                fun_idx,
            })
        }

        mono::Expr::AssocFnSelect(mono::AssocFnSelectExpr {
            ty,
            member,
            ty_args,
        }) => Expr::AssocFnSelect(
            *indices
                .assoc_fun_nums
                .get(ty)
                .unwrap()
                .get(member)
                .unwrap()
                .get(ty_args)
                .unwrap(),
        ),

        mono::Expr::Call(mono::CallExpr { fun, args }) => Expr::Call(CallExpr {
            fun: lower_bl_expr(fun, indices),
            args: args
                .iter()
                .map(|mono::CallArg { name, expr }| CallArg {
                    name: name.clone(),
                    expr: lower_l_expr(expr, indices),
                })
                .collect(),
        }),

        mono::Expr::Int(int) => Expr::Int(int.clone()),

        mono::Expr::String(parts) => Expr::String(
            parts
                .iter()
                .map(|part| match part {
                    mono::StringPart::Str(str) => StringPart::Str(str.clone()),
                    mono::StringPart::Expr(expr) => StringPart::Expr(lower_l_expr(expr, indices)),
                })
                .collect(),
        ),

        mono::Expr::Char(char) => Expr::Char(*char),

        mono::Expr::Self_ => Expr::Self_,

        mono::Expr::BinOp(mono::BinOpExpr {
            left,
            right,
            op: mono::BinOp::And,
        }) => Expr::BoolAnd(lower_bl_expr(left, indices), lower_bl_expr(right, indices)),

        mono::Expr::BinOp(mono::BinOpExpr {
            left,
            right,
            op: mono::BinOp::Or,
        }) => Expr::BoolOr(lower_bl_expr(left, indices), lower_bl_expr(right, indices)),

        mono::Expr::BinOp(_) => panic!("Non-desugared BinOp"),

        mono::Expr::UnOp(_) => panic!("Non-desugared UnOp"),

        mono::Expr::Record(fields) => Expr::Record(
            fields
                .iter()
                .map(|field| lower_nl_expr(field, indices))
                .collect(),
        ),

        mono::Expr::Variant(mono::VariantExpr { id, args }) => Expr::Variant(VariantExpr {
            id: id.clone(),
            args: args.iter().map(|arg| lower_nl_expr(arg, indices)).collect(),
        }),

        mono::Expr::Return(expr) => Expr::Return(lower_bl_expr(expr, indices)),

        mono::Expr::Match(mono::MatchExpr { scrutinee, alts }) => Expr::Match(MatchExpr {
            scrutinee: lower_bl_expr(scrutinee, indices),
            alts: alts
                .iter()
                .map(
                    |mono::Alt {
                         pattern,
                         guard,
                         rhs,
                     }| Alt {
                        pattern: lower_l_pat(pattern, indices),
                        guard: guard.as_ref().map(|guard| lower_l_expr(guard, indices)),
                        rhs: rhs.iter().map(|stmt| lower_l_stmt(stmt, indices)).collect(),
                    },
                )
                .collect(),
        }),

        mono::Expr::If(mono::IfExpr {
            branches,
            else_branch,
        }) => Expr::If(IfExpr {
            branches: branches
                .iter()
                .map(|(cond, rhs)| {
                    (
                        lower_l_expr(cond, indices),
                        rhs.iter().map(|stmt| lower_l_stmt(stmt, indices)).collect(),
                    )
                })
                .collect(),
            else_branch: else_branch.as_ref().map(|stmts| {
                stmts
                    .iter()
                    .map(|stmt| lower_l_stmt(stmt, indices))
                    .collect()
            }),
        }),

        mono::Expr::Fn(mono::FnExpr { .. }) => todo!(),
    }
}

fn lower_nl_expr(expr: &Named<L<mono::Expr>>, indices: &mut Indices) -> Named<L<Expr>> {
    expr.map_as_ref(|expr| lower_l_expr(expr, indices))
}

fn lower_l_expr(expr: &L<mono::Expr>, indices: &mut Indices) -> L<Expr> {
    expr.map_as_ref(|expr| lower_expr(expr, indices))
}

fn lower_bl_expr(expr: &Box<L<mono::Expr>>, indices: &mut Indices) -> Box<L<Expr>> {
    Box::new(expr.map_as_ref(|expr| lower_expr(expr, indices)))
}

fn lower_pat(pat: &mono::Pat, indices: &mut Indices) -> Pat {
    match pat {
        mono::Pat::Var(var) => {
            let var_idx = LocalIdx(indices.local_nums.len() as u32);
            indices.local_nums.insert(var.clone(), var_idx);
            Pat::Var(var_idx)
        }

        mono::Pat::Constr(mono::ConstrPattern {
            constr: mono::Constructor { type_, constr },
            fields,
            ty_args,
        }) => {
            let con_idx: ConIdx = match constr {
                Some(constr) => *indices
                    .sum_con_nums
                    .get(type_)
                    .unwrap()
                    .get(constr)
                    .unwrap()
                    .get(ty_args)
                    .unwrap(),
                None => *indices
                    .product_con_nums
                    .get(type_)
                    .unwrap()
                    .get(ty_args)
                    .unwrap(),
            };
            Pat::Constr(ConstrPattern {
                constr: con_idx,
                fields: fields
                    .iter()
                    .map(|named_f| named_f.map_as_ref(|f| lower_l_pat(f, indices)))
                    .collect(),
            })
        }

        mono::Pat::Variant(mono::VariantPattern { constr, fields }) => {
            Pat::Variant(VariantPattern {
                constr: constr.clone(),
                fields: fields
                    .iter()
                    .map(|field| lower_nl_pat(field, indices))
                    .collect(),
            })
        }

        mono::Pat::Record(fields) => Pat::Record(
            fields
                .iter()
                .map(|field| lower_nl_pat(field, indices))
                .collect(),
        ),

        mono::Pat::Ignore => Pat::Ignore,

        mono::Pat::Str(str) => Pat::Str(str.clone()),

        mono::Pat::Char(char) => Pat::Char(*char),

        mono::Pat::StrPfx(str, var) => {
            let var_idx = LocalIdx(indices.local_nums.len() as u32);
            indices.local_nums.insert(var.clone(), var_idx);
            Pat::StrPfx(str.clone(), var_idx)
        }

        mono::Pat::Or(p1, p2) => Pat::Or(
            Box::new(lower_l_pat(p1, indices)),
            Box::new(lower_l_pat(p2, indices)),
        ),
    }
}

fn lower_nl_pat(pat: &Named<L<mono::Pat>>, indices: &mut Indices) -> Named<L<Pat>> {
    pat.map_as_ref(|pat| lower_l_pat(pat, indices))
}

fn lower_l_pat(pat: &L<mono::Pat>, indices: &mut Indices) -> L<Pat> {
    pat.map_as_ref(|pat| lower_pat(pat, indices))
}

fn lower_source_fun(
    fun: &mono::FunDecl,
    idx: FunIdx,
    ty_args: &Vec<mono::Type>,
    indices: &mut Indices,
) -> SourceFunDecl {
    let mut locals: Vec<LocalInfo> = vec![];
    let mut local_nums: Map<Id, LocalIdx> = Default::default();

    if !matches!(fun.sig.self_, mono::SelfParam::No) {
        locals.push(LocalInfo {
            name: SmolStr::new_static("self"),
            ty: mono::Type::Record { fields: vec![] }, // TODO
        });
        local_nums.insert(SmolStr::new_static("self"), LocalIdx(0));
    }

    for (param, ty) in &fun.sig.params {
        locals.push(LocalInfo {
            name: param.clone(),
            ty: ty.node.clone(),
        });
        local_nums.insert(param.clone(), LocalIdx(local_nums.len() as u32));
    }

    let body: Vec<L<Stmt>> = fun
        .body
        .as_ref()
        .unwrap()
        .iter()
        .map(|stmt| lower_l_stmt(stmt, indices))
        .collect();

    let params: Vec<Ty> = locals.iter().map(|l| Ty::from_mono_ty(&l.ty)).collect();

    SourceFunDecl {
        parent_ty: fun.parent_ty.clone(),
        name: fun.name.clone(),
        idx,
        ty_args: ty_args.clone(),
        locals,
        body,
        params,

        // Implicit return types should've been made implicit in a previous pass.
        return_ty: fun
            .sig
            .return_ty
            .as_ref()
            .map(|l| Ty::from_mono_ty(&l.node))
            .unwrap(),

        // Constructors don't have exception types as they cannot throw, and their type parameters
        // need to be the same as the constructed type's type parameters. We can assume their
        // exception type to be empty type (variant with no constructor).
        exceptions: fun
            .sig
            .exceptions
            .as_ref()
            .map(|ty| Ty::from_mono_ty(&ty.node))
            .unwrap_or(Ty {
                mono_ty: mono::Type::Variant { alts: vec![] },
                repr: Repr::U64, // TODO: should this be void?
            }),
    }
}
