//! Numbering pass lowers monomorphic AST to eliminate type arguments. All function and consturctor
//! references are converted into indices by this pass.

pub mod printer;

use crate::collections::*;
use crate::mono_ast::{self as mono, AssignOp, BinOp, Id, IntExpr, Named, UnOp, L};
use crate::record_collector::{collect_records, RecordShape, VariantShape};
use crate::utils::loc_display;

use smol_str::SmolStr;

#[derive(Debug)]
pub struct LoweredPgm {
    cons: Vec<Con>,
    funs: Vec<Fun>,
    closures: Vec<Closure>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FunIdx(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ConIdx(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LocalIdx(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ClosureIdx(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RecordIdx(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VariantIdx(u32);

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
    Builtin(BuiltinFunDecl),
    Source(SourceFunDecl),
}

#[derive(Debug)]
pub enum BuiltinFunDecl {
    Panic,
    PrintStr,
    ShrI8,
    ShrU8,
    ShrI32,
    ShrU32,
    BitAndI8,
    BitAndU8,
    BitAndI32,
    BitAndU32,
    BitOrI8,
    BitOrU8,
    BitOrI32,
    BitOrU32,
    ToStrI8,
    ToStrU8,
    ToStrI32,
    ToStrU32,
    U8AsU32,
    U32AsU8,
    I8Shl,
    U8Shl,
    I32Shl,
    U32Shl,
    I8Cmp,
    U8Cmp,
    I32Cmp,
    U32Cmp,
    I8Add,
    U8Add,
    I32Add,
    U32Add,
    I8Sub,
    U8Sub,
    I32Sub,
    U32Sub,
    I8Mul,
    U8Mul,
    I32Mul,
    U32Mul,
    I8Div,
    U8Div,
    I32Div,
    U32Div,
    I8Eq,
    U8Eq,
    I32Eq,
    U32Eq,

    /// `prim throw(exn: [..r]): {..r} a`
    Throw {
        /// The error rows in the exception argument: `exn: [..r]`.
        r: mono::Type,

        /// The return type.
        a: mono::Type,
    },

    /// `prim try(cb: Fn(): {..exn} a): {..r} Result[[..exn], a]`
    Try {
        /// Type of exceptions to catch.
        exn: mono::Type,

        /// The return type of the callback.
        a: mono::Type,

        /// The expected exception type in the call site.
        r: mono::Type,
    },

    ArrayNew {
        t: mono::Type,
    },

    ArrayLen,

    ArrayGet {
        t: mono::Type,
    },

    ArraySet {
        t: mono::Type,
    },
}

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
    BoolNot(Box<L<Expr>>),
    BoolAnd(Box<L<Expr>>, Box<L<Expr>>),
    BoolOr(Box<L<Expr>>, Box<L<Expr>>),
    Record(RecordExpr),
    Variant(VariantExpr),
    Return(Box<L<Expr>>),
    Match(MatchExpr),
    If(IfExpr),
    ClosureAlloc(ClosureIdx),
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
pub struct RecordExpr {
    pub fields: Vec<Named<L<Expr>>>,
    pub idx: RecordIdx,
}

#[derive(Debug, Clone)]
pub struct VariantExpr {
    pub id: Id,
    pub fields: Vec<Named<L<Expr>>>,
    pub idx: VariantIdx,
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
    Record(RecordPattern),
    Variant(VariantPattern),
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
pub struct RecordPattern {
    pub fields: Vec<Named<L<Pat>>>,
    pub idx: RecordIdx,
}

#[derive(Debug, Clone)]
pub struct VariantPattern {
    pub constr: Id,
    pub fields: Vec<Named<L<Pat>>>,
    pub idx: VariantIdx,
}

#[derive(Debug)]
pub struct Closure {
    pub idx: ClosureIdx, // for debugging

    /// Locals of the closure: both captured variables and arguments.
    ///
    /// Captured variables come first, then arguments.
    pub locals: Vec<Id>, // for debugging, indexed by `LocalIdx`

    pub fvs: Vec<ClosureFv>,
    pub params: Vec<Ty>,
    pub body: Vec<L<Stmt>>,
}

/// A free variable in a closure.
#[derive(Debug, Clone)]
pub struct ClosureFv {
    /// Id of the free variable, for debugging.
    pub id: Id,

    /// Index of the local in the closure allocation site.
    pub alloc_idx: LocalIdx,

    /// Index of the local in closure's locals.
    ///
    /// This is also the index in the closure's heap object payload.
    pub use_idx: LocalIdx,
}

////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
struct Indices {
    product_cons: Map<Id, Map<Vec<mono::Type>, ConIdx>>,
    sum_cons: Map<Id, Map<Id, Map<Vec<mono::Type>, ConIdx>>>,
    funs: Map<Id, Map<Vec<mono::Type>, FunIdx>>,
    assoc_funs: Map<Id, Map<Id, Map<Vec<mono::Type>, FunIdx>>>,
    locals: Map<Id, LocalIdx>,
    records: Map<RecordShape, RecordIdx>,
    variants: Map<VariantShape, VariantIdx>,
}

pub fn lower(mono_pgm: &mut mono::MonoPgm) -> LoweredPgm {
    let (record_shapes, variant_shapes) = collect_records(mono_pgm);

    let record_indices: Map<RecordShape, RecordIdx> = record_shapes
        .into_iter()
        .zip(std::iter::successors(Some(RecordIdx(0)), |i| {
            Some(RecordIdx(i.0 + 1))
        }))
        .collect();

    let variant_indices: Map<VariantShape, VariantIdx> = variant_shapes
        .into_iter()
        .zip(std::iter::successors(Some(VariantIdx(0)), |i| {
            Some(VariantIdx(i.0 + 1))
        }))
        .collect();

    // Number all declarations first, then lower the program.
    let mut product_con_nums: Map<Id, Map<Vec<mono::Type>, ConIdx>> = Default::default();
    let mut sum_con_nums: Map<Id, Map<Id, Map<Vec<mono::Type>, ConIdx>>> = Default::default();
    let mut fun_nums: Map<Id, Map<Vec<mono::Type>, FunIdx>> = Default::default();
    let mut assoc_fun_nums: Map<Id, Map<Id, Map<Vec<mono::Type>, FunIdx>>> = Default::default();

    // Number type declarations.
    let mut next_con_idx = ConIdx(0);
    for (con_id, con_ty_map) in &mono_pgm.ty {
        for (con_ty_args, con_decl) in con_ty_map {
            match &con_decl.rhs {
                Some(mono::TypeDeclRhs::Sum(cons)) => {
                    for con in cons {
                        sum_con_nums
                            .entry(con_id.clone())
                            .or_default()
                            .entry(con.name.clone())
                            .or_default()
                            .entry(con_ty_args.clone())
                            .or_insert_with(|| {
                                let idx = next_con_idx;
                                next_con_idx = ConIdx(next_con_idx.0 + 1);
                                idx
                            });
                    }
                }

                Some(mono::TypeDeclRhs::Product(_)) | None => {
                    // No RHS means it's either an uninhabited type like Void or a primitive. We
                    // can't distinguish the two here, so we assume primitive and give a number to
                    // all types without a RHS.
                    product_con_nums
                        .entry(con_id.clone())
                        .or_default()
                        .entry(con_ty_args.clone())
                        .or_insert_with(|| {
                            let idx = next_con_idx;
                            next_con_idx = ConIdx(next_con_idx.0 + 1);
                            idx
                        });
                }
            }
        }
    }

    // Number top-level functions.
    let mut next_fun_idx = FunIdx(0);
    for (fun_id, fun_ty_map) in &mono_pgm.funs {
        for (fun_ty_args, _fun_decl) in fun_ty_map {
            fun_nums
                .entry(fun_id.clone())
                .or_default()
                .entry(fun_ty_args.clone())
                .or_insert_with(|| {
                    let idx = next_fun_idx;
                    next_fun_idx = FunIdx(next_fun_idx.0 + 1);
                    idx
                });
        }
    }

    // Number associated functions.
    for (fun_ty_id, assoc_fn_map) in &mono_pgm.associated {
        for (fun_id, fun_ty_map) in assoc_fn_map {
            for (fun_ty_args, _fun_decl) in fun_ty_map {
                assoc_fun_nums
                    .entry(fun_ty_id.clone())
                    .or_default()
                    .entry(fun_id.clone())
                    .or_default()
                    .entry(fun_ty_args.clone())
                    .or_insert_with(|| {
                        let idx = next_fun_idx;
                        next_fun_idx = FunIdx(next_fun_idx.0 + 1);
                        idx
                    });
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

                    "I8" => {
                        assert_eq!(con_ty_args.len(), 0);
                        lowered_pgm.cons.push(Con::Builtin(BuiltinConDecl::I8));
                    }

                    "U8" => {
                        assert_eq!(con_ty_args.len(), 0);
                        lowered_pgm.cons.push(Con::Builtin(BuiltinConDecl::U8));
                    }

                    "I32" => {
                        assert_eq!(con_ty_args.len(), 0);
                        lowered_pgm.cons.push(Con::Builtin(BuiltinConDecl::I32));
                    }

                    "U32" => {
                        assert_eq!(con_ty_args.len(), 0);
                        lowered_pgm.cons.push(Con::Builtin(BuiltinConDecl::U32));
                    }

                    "Void" => {
                        assert_eq!(con_ty_args.len(), 0);
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
        product_cons: product_con_nums,
        sum_cons: sum_con_nums,
        funs: fun_nums,
        assoc_funs: assoc_fun_nums,
        locals: Default::default(), // updated in each function
        records: record_indices,
        variants: variant_indices,
    };

    // Lower top-level functions.
    for (fun_id, fun_ty_map) in &mono_pgm.funs {
        for (fun_ty_args, fun_decl) in fun_ty_map {
            let idx = FunIdx(lowered_pgm.funs.len() as u32);
            if fun_decl.body.is_some() {
                let source_fun = lower_source_fun(
                    fun_decl,
                    idx,
                    fun_ty_args,
                    &mut indices,
                    &mut lowered_pgm.closures,
                );
                lowered_pgm.funs.push(Fun::Source(source_fun));
            } else {
                match fun_id.as_str() {
                    "printStr" => {
                        assert_eq!(fun_ty_args.len(), 1); // exception
                        lowered_pgm
                            .funs
                            .push(Fun::Builtin(BuiltinFunDecl::PrintStr));
                    }

                    "panic" => {
                        assert_eq!(fun_ty_args.len(), 2); // ToStr, exception
                        lowered_pgm.funs.push(Fun::Builtin(BuiltinFunDecl::Panic));
                    }

                    "try" => {
                        //  prim try(cb: Fn(): {..exn} a): {..r} Result[[..exn], a]
                        assert_eq!(fun_ty_args.len(), 3); // exn, a, r
                        let exn = fun_ty_args[0].clone();
                        let a = fun_ty_args[1].clone();
                        let r = fun_ty_args[2].clone();
                        lowered_pgm
                            .funs
                            .push(Fun::Builtin(BuiltinFunDecl::Try { exn, a, r }));
                    }

                    "throw" => {
                        // prim throw(exn: [..r]): {..r} a
                        assert_eq!(fun_ty_args.len(), 2); // r, a
                        let r = fun_ty_args[0].clone();
                        let a = fun_ty_args[1].clone();
                        lowered_pgm
                            .funs
                            .push(Fun::Builtin(BuiltinFunDecl::Throw { r, a }));
                    }

                    other => {
                        panic!(
                            "Unknown built-in function: {} (ty args = {:?})",
                            other, fun_ty_args
                        );
                    }
                }
            }
        }
    }

    // Number associated functions.
    for (ty, assoc_fun_map) in &mono_pgm.associated {
        for (fun, fun_ty_map) in assoc_fun_map {
            for (fun_ty_args, fun_decl) in fun_ty_map {
                let idx = FunIdx(lowered_pgm.funs.len() as u32);
                if fun_decl.body.is_some() {
                    let source_fun = lower_source_fun(
                        fun_decl,
                        idx,
                        fun_ty_args,
                        &mut indices,
                        &mut lowered_pgm.closures,
                    );
                    lowered_pgm.funs.push(Fun::Source(source_fun));
                } else {
                    match (ty.as_str(), fun.as_str()) {
                        ("Shr", "__shr") => {
                            assert_eq!(fun_ty_args.len(), 2); // self, exception
                            match &fun_ty_args[0] {
                                mono::Type::Named(mono::NamedType { name, args }) => {
                                    match name.as_str() {
                                        "I8" => {
                                            assert!(args.is_empty());
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::ShrI8));
                                        }
                                        "U8" => {
                                            assert!(args.is_empty());
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::ShrU8));
                                        }
                                        "I32" => {
                                            assert!(args.is_empty());
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::ShrI32));
                                        }
                                        "U32" => {
                                            assert!(args.is_empty());
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::ShrU32));
                                        }
                                        _ => panic!(),
                                    }
                                }
                                _ => panic!(),
                            }
                        }

                        ("BitAnd", "__bitand") => {
                            assert_eq!(fun_ty_args.len(), 2); // self, exception
                            match &fun_ty_args[0] {
                                mono::Type::Named(mono::NamedType { name, args }) => {
                                    match name.as_str() {
                                        "I8" => {
                                            assert!(args.is_empty());
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::BitAndI8));
                                        }
                                        "U8" => {
                                            assert!(args.is_empty());
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::BitAndU8));
                                        }
                                        "I32" => {
                                            assert!(args.is_empty());
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::BitAndI32));
                                        }
                                        "U32" => {
                                            assert!(args.is_empty());
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::BitAndU32));
                                        }
                                        _ => panic!(),
                                    }
                                }
                                _ => panic!(),
                            }
                        }

                        ("BitOr", "__bitor") => {
                            assert_eq!(fun_ty_args.len(), 2); // self, exception
                            match &fun_ty_args[0] {
                                mono::Type::Named(mono::NamedType { name, args }) => {
                                    match name.as_str() {
                                        "I8" => {
                                            assert!(args.is_empty());
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::BitOrI8));
                                        }
                                        "U8" => {
                                            assert!(args.is_empty());
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::BitOrU8));
                                        }
                                        "I32" => {
                                            assert!(args.is_empty());
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::BitOrI32));
                                        }
                                        "U32" => {
                                            assert!(args.is_empty());
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::BitOrU32));
                                        }
                                        _ => panic!(),
                                    }
                                }
                                _ => panic!(),
                            }
                        }

                        ("ToStr", "toStr") => {
                            assert_eq!(fun_ty_args.len(), 2); // self, exception
                            match &fun_ty_args[0] {
                                mono::Type::Named(mono::NamedType { name, args }) => {
                                    match name.as_str() {
                                        "I8" => {
                                            assert!(args.is_empty());
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::ToStrI8));
                                        }
                                        "U8" => {
                                            assert!(args.is_empty());
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::ToStrU8));
                                        }
                                        "I32" => {
                                            assert!(args.is_empty());
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::ToStrI32));
                                        }
                                        "U32" => {
                                            assert!(args.is_empty());
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::ToStrU32));
                                        }
                                        _ => panic!(),
                                    }
                                }
                                _ => panic!(),
                            }
                        }

                        ("U32", "asU8") => {
                            assert_eq!(fun_ty_args.len(), 1); // exception
                            lowered_pgm.funs.push(Fun::Builtin(BuiltinFunDecl::U32AsU8));
                        }

                        ("U8", "asU32") => {
                            assert_eq!(fun_ty_args.len(), 1); // exception
                            lowered_pgm.funs.push(Fun::Builtin(BuiltinFunDecl::U8AsU32));
                        }

                        ("Shl", "__shl") => {
                            assert_eq!(fun_ty_args.len(), 2); // self, exception
                            match &fun_ty_args[0] {
                                mono::Type::Named(mono::NamedType { name, args: _ }) => {
                                    match name.as_str() {
                                        "I8" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::I8Shl));
                                        }

                                        "U8" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::U8Shl));
                                        }

                                        "I32" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::I32Shl));
                                        }

                                        "U32" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::U32Shl));
                                        }

                                        _ => panic!(),
                                    }
                                }
                                _ => panic!(),
                            }
                        }

                        ("Ord", "cmp") => {
                            assert_eq!(fun_ty_args.len(), 2); // self, exception
                            match &fun_ty_args[0] {
                                mono::Type::Named(mono::NamedType { name, args: _ }) => {
                                    match name.as_str() {
                                        "I8" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::I8Cmp));
                                        }

                                        "U8" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::U8Cmp));
                                        }

                                        "I32" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::I32Cmp));
                                        }

                                        "U32" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::U32Cmp));
                                        }

                                        _ => panic!(),
                                    }
                                }
                                _ => panic!(),
                            }
                        }

                        ("Add", "__add") => {
                            assert_eq!(fun_ty_args.len(), 2); // self, exception
                            match &fun_ty_args[0] {
                                mono::Type::Named(mono::NamedType { name, args: _ }) => {
                                    match name.as_str() {
                                        "I8" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::I8Add));
                                        }

                                        "U8" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::U8Add));
                                        }

                                        "I32" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::I32Add));
                                        }

                                        "U32" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::U32Add));
                                        }

                                        _ => panic!(),
                                    }
                                }

                                _ => panic!(),
                            }
                        }

                        ("Sub", "__sub") => {
                            assert_eq!(fun_ty_args.len(), 2); // self, exception
                            match &fun_ty_args[0] {
                                mono::Type::Named(mono::NamedType { name, args: _ }) => {
                                    match name.as_str() {
                                        "I8" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::I8Sub));
                                        }

                                        "U8" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::U8Sub));
                                        }

                                        "I32" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::I32Sub));
                                        }

                                        "U32" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::U32Sub));
                                        }

                                        _ => panic!(),
                                    }
                                }

                                _ => panic!(),
                            }
                        }

                        ("Mul", "__mul") => {
                            assert_eq!(fun_ty_args.len(), 2); // self, exception
                            match &fun_ty_args[0] {
                                mono::Type::Named(mono::NamedType { name, args: _ }) => {
                                    match name.as_str() {
                                        "I8" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::I8Mul));
                                        }

                                        "U8" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::U8Mul));
                                        }

                                        "I32" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::I32Mul));
                                        }

                                        "U32" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::U32Mul));
                                        }

                                        _ => panic!(),
                                    }
                                }
                                _ => panic!(),
                            }
                        }

                        ("Div", "__div") => {
                            assert_eq!(fun_ty_args.len(), 2); // self, exception
                            match &fun_ty_args[0] {
                                mono::Type::Named(mono::NamedType { name, args: _ }) => {
                                    match name.as_str() {
                                        "I8" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::I8Div));
                                        }

                                        "U8" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::U8Div));
                                        }

                                        "I32" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::I32Div));
                                        }

                                        "U32" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::U32Div));
                                        }

                                        _ => panic!(),
                                    }
                                }
                                _ => panic!(),
                            }
                        }

                        ("Eq", "__eq") => {
                            assert_eq!(fun_ty_args.len(), 2); // self, exception
                            match &fun_ty_args[0] {
                                mono::Type::Named(mono::NamedType { name, args: _ }) => {
                                    match name.as_str() {
                                        "I8" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::I8Eq));
                                        }

                                        "U8" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::U8Eq));
                                        }

                                        "I32" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::I32Eq));
                                        }

                                        "U32" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::U32Eq));
                                        }

                                        _ => panic!(),
                                    }
                                }

                                _ => panic!(),
                            }
                        }

                        ("Array", "new") => {
                            // prim Array.new(len: U32): Array[t]
                            assert_eq!(fun_ty_args.len(), 2); // t, exception (implicit)
                            let t = fun_ty_args[1].clone();
                            lowered_pgm
                                .funs
                                .push(Fun::Builtin(BuiltinFunDecl::ArrayNew { t }));
                        }

                        ("Array", "len") => {
                            // prim Array.len(self: Array[t]): U32
                            assert_eq!(fun_ty_args.len(), 2); // t, exception (implicit)
                                                              // All arrays have the length in the same location, ignore `t`.
                            lowered_pgm
                                .funs
                                .push(Fun::Builtin(BuiltinFunDecl::ArrayLen));
                        }

                        ("Array", "get") => {
                            // prim Array.get(self: Array[t], idx: U32): t
                            assert_eq!(fun_ty_args.len(), 2); // t, exception (implicit)
                            let t = fun_ty_args[0].clone();
                            lowered_pgm
                                .funs
                                .push(Fun::Builtin(BuiltinFunDecl::ArrayGet { t }));
                        }

                        ("Array", "set") => {
                            // prim Array.set(self: Array[t], idx: U32, elem: t)
                            assert_eq!(fun_ty_args.len(), 2); // t, exception (implicit)
                            let t = fun_ty_args[0].clone();
                            lowered_pgm
                                .funs
                                .push(Fun::Builtin(BuiltinFunDecl::ArraySet { t }));
                        }

                        (_, _) => todo!("Built-in function {}.{}", ty, fun),
                    }
                }
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

fn lower_stmt(
    stmt: &mono::Stmt,
    closures: &mut Vec<Closure>,
    local_vars: &mut ScopeSet<Id>,
    free_vars: &mut Map<Id, LocalIdx>,
    indices: &mut Indices,
) -> Stmt {
    match stmt {
        mono::Stmt::Let(mono::LetStmt { lhs, rhs }) => Stmt::Let(LetStmt {
            lhs: lower_l_pat(lhs, local_vars, indices),
            rhs: lower_l_expr(rhs, closures, local_vars, free_vars, indices),
        }),

        mono::Stmt::Assign(mono::AssignStmt { lhs, rhs, op }) => Stmt::Assign(AssignStmt {
            lhs: lower_l_expr(lhs, closures, local_vars, free_vars, indices),
            rhs: lower_l_expr(rhs, closures, local_vars, free_vars, indices),
            op: *op,
        }),

        mono::Stmt::Expr(expr) => {
            Stmt::Expr(lower_l_expr(expr, closures, local_vars, free_vars, indices))
        }

        mono::Stmt::For(mono::ForStmt {
            label,
            pat,
            expr,
            body,
        }) => {
            let expr = lower_l_expr(expr, closures, local_vars, free_vars, indices);

            local_vars.enter();
            let pat = lower_l_pat(pat, local_vars, indices);
            let body = body
                .iter()
                .map(|stmt| lower_l_stmt(stmt, closures, local_vars, free_vars, indices))
                .collect();
            local_vars.exit();

            Stmt::For(ForStmt {
                label: label.clone(),
                pat,
                expr,
                body,
            })
        }

        mono::Stmt::While(mono::WhileStmt { label, cond, body }) => Stmt::While(WhileStmt {
            label: label.clone(),
            cond: lower_l_expr(cond, closures, local_vars, free_vars, indices),
            body: body
                .iter()
                .map(|stmt| lower_l_stmt(stmt, closures, local_vars, free_vars, indices))
                .collect(),
        }),

        mono::Stmt::WhileLet(mono::WhileLetStmt {
            label,
            pat,
            cond,
            body,
        }) => {
            let cond = lower_l_expr(cond, closures, local_vars, free_vars, indices);

            local_vars.enter();
            let pat = lower_l_pat(pat, local_vars, indices);
            let body = body
                .iter()
                .map(|stmt| lower_l_stmt(stmt, closures, local_vars, free_vars, indices))
                .collect();
            local_vars.exit();

            Stmt::WhileLet(WhileLetStmt {
                label: label.clone(),
                pat,
                cond,
                body,
            })
        }

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

fn lower_l_stmt(
    stmt: &L<mono::Stmt>,
    closures: &mut Vec<Closure>,
    local_vars: &mut ScopeSet<Id>,
    free_vars: &mut Map<Id, LocalIdx>,
    indices: &mut Indices,
) -> L<Stmt> {
    stmt.map_as_ref(|stmt| lower_stmt(stmt, closures, local_vars, free_vars, indices))
}

/// - `closures`: The closures collected so far.
///
/// - `local_vars`: Local variables of the current function: arguments, binders in patterns and
///   `let` statements.
///
/// - `free_vars`: Free variables of the current function: any variables that are not arguments of
///   the current function and not bound in the current function.
fn lower_expr(
    expr: &mono::Expr,
    loc: &mono::Loc,
    closures: &mut Vec<Closure>,
    local_vars: &mut ScopeSet<Id>,
    free_vars: &mut Map<Id, LocalIdx>,
    indices: &mut Indices,
) -> Expr {
    match expr {
        mono::Expr::LocalVar(var) => {
            if !local_vars.is_bound(var) {
                let idx = LocalIdx(free_vars.len() as u32);
                free_vars.insert(var.clone(), idx);
                Expr::LocalVar(idx)
            } else {
                Expr::LocalVar(*indices.locals.get(var).unwrap_or_else(|| {
                    panic!(
                        "{}: BUG: Variable {} is not in local nums ({:?})",
                        loc_display(loc),
                        var,
                        indices.locals,
                    )
                }))
            }
        }

        mono::Expr::TopVar(mono::VarExpr { id, ty_args }) => {
            Expr::TopVar(*indices.funs.get(id).unwrap().get(ty_args).unwrap())
        }

        mono::Expr::Constr(mono::ConstrExpr { id, ty_args }) => {
            Expr::Constr(*indices.product_cons.get(id).unwrap().get(ty_args).unwrap())
        }

        mono::Expr::ConstrSelect(mono::ConstrSelectExpr {
            ty,
            constr,
            ty_args,
        }) => Expr::Constr(
            *indices
                .sum_cons
                .get(ty)
                .unwrap()
                .get(constr)
                .unwrap()
                .get(ty_args)
                .unwrap(),
        ),

        mono::Expr::FieldSelect(mono::FieldSelectExpr { object, field }) => {
            Expr::FieldSelect(FieldSelectExpr {
                object: lower_bl_expr(object, closures, local_vars, free_vars, indices),
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
                .assoc_funs
                .get(method_ty_id)
                .unwrap()
                .get(method_id)
                .unwrap()
                .get(ty_args)
                .unwrap();

            Expr::MethodSelect(MethodSelectExpr {
                object: lower_bl_expr(object, closures, local_vars, free_vars, indices),
                fun_idx,
            })
        }

        mono::Expr::AssocFnSelect(mono::AssocFnSelectExpr {
            ty,
            member,
            ty_args,
        }) => Expr::AssocFnSelect(
            *indices
                .assoc_funs
                .get(ty)
                .unwrap()
                .get(member)
                .unwrap()
                .get(ty_args)
                .unwrap(),
        ),

        mono::Expr::Call(mono::CallExpr { fun, args }) => Expr::Call(CallExpr {
            fun: lower_bl_expr(fun, closures, local_vars, free_vars, indices),
            args: args
                .iter()
                .map(|mono::CallArg { name, expr }| CallArg {
                    name: name.clone(),
                    expr: lower_l_expr(expr, closures, local_vars, free_vars, indices),
                })
                .collect(),
        }),

        mono::Expr::Int(int) => Expr::Int(int.clone()),

        mono::Expr::String(parts) => Expr::String(
            parts
                .iter()
                .map(|part| match part {
                    mono::StringPart::Str(str) => StringPart::Str(str.clone()),
                    mono::StringPart::Expr(expr) => StringPart::Expr(lower_l_expr(
                        expr, closures, local_vars, free_vars, indices,
                    )),
                })
                .collect(),
        ),

        mono::Expr::Char(char) => Expr::Char(*char),

        mono::Expr::Self_ => Expr::Self_,

        mono::Expr::BinOp(mono::BinOpExpr {
            left,
            right,
            op: mono::BinOp::And,
        }) => Expr::BoolAnd(
            lower_bl_expr(left, closures, local_vars, free_vars, indices),
            lower_bl_expr(right, closures, local_vars, free_vars, indices),
        ),

        mono::Expr::BinOp(mono::BinOpExpr {
            left,
            right,
            op: mono::BinOp::Or,
        }) => Expr::BoolOr(
            lower_bl_expr(left, closures, local_vars, free_vars, indices),
            lower_bl_expr(right, closures, local_vars, free_vars, indices),
        ),

        mono::Expr::BinOp(_) => panic!("Non-desugared BinOp"),

        mono::Expr::UnOp(mono::UnOpExpr { op, expr }) => match op {
            UnOp::Neg => panic!("Neg unop wasn't desugred"),
            UnOp::Not => Expr::BoolNot(lower_bl_expr(
                expr, closures, local_vars, free_vars, indices,
            )),
        },

        mono::Expr::Record(fields) => {
            let idx = *indices
                .records
                .get(&RecordShape::from_named_things(fields))
                .unwrap();
            Expr::Record(RecordExpr {
                fields: fields
                    .iter()
                    .map(|field| lower_nl_expr(field, closures, local_vars, free_vars, indices))
                    .collect(),
                idx,
            })
        }

        mono::Expr::Variant(mono::VariantExpr { id, args }) => {
            let idx = *indices
                .variants
                .get(&VariantShape::from_con_and_fields(id, args))
                .unwrap();
            Expr::Variant(VariantExpr {
                id: id.clone(),
                fields: args
                    .iter()
                    .map(|arg| lower_nl_expr(arg, closures, local_vars, free_vars, indices))
                    .collect(),
                idx,
            })
        }

        mono::Expr::Return(expr) => Expr::Return(lower_bl_expr(
            expr, closures, local_vars, free_vars, indices,
        )),

        mono::Expr::Match(mono::MatchExpr { scrutinee, alts }) => Expr::Match(MatchExpr {
            scrutinee: lower_bl_expr(scrutinee, closures, local_vars, free_vars, indices),
            alts: alts
                .iter()
                .map(
                    |mono::Alt {
                         pattern,
                         guard,
                         rhs,
                     }| {
                        local_vars.enter();
                        let pattern = lower_l_pat(pattern, local_vars, indices);
                        let guard = guard.as_ref().map(|guard| {
                            lower_l_expr(guard, closures, local_vars, free_vars, indices)
                        });
                        let rhs = rhs
                            .iter()
                            .map(|stmt| {
                                lower_l_stmt(stmt, closures, local_vars, free_vars, indices)
                            })
                            .collect();
                        local_vars.exit();
                        Alt {
                            pattern,
                            guard,
                            rhs,
                        }
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
                        lower_l_expr(cond, closures, local_vars, free_vars, indices),
                        rhs.iter()
                            .map(|stmt| {
                                lower_l_stmt(stmt, closures, local_vars, free_vars, indices)
                            })
                            .collect(),
                    )
                })
                .collect(),
            else_branch: else_branch.as_ref().map(|stmts| {
                stmts
                    .iter()
                    .map(|stmt| lower_l_stmt(stmt, closures, local_vars, free_vars, indices))
                    .collect()
            }),
        }),

        mono::Expr::Fn(mono::FnExpr { sig, body }) => {
            let mut fn_local_vars: ScopeSet<Id> = Default::default();
            for (param, _) in &sig.params {
                fn_local_vars.insert(param.clone());
            }

            let mut fn_free_vars: Map<Id, LocalIdx> = Default::default();

            let body: Vec<L<Stmt>> = body
                .iter()
                .map(|stmt| {
                    lower_l_stmt(
                        stmt,
                        closures,
                        &mut fn_local_vars,
                        &mut fn_free_vars,
                        indices,
                    )
                })
                .collect();

            let closure_idx = ClosureIdx(closures.len() as u32);

            let mut fn_free_vars_sorted: Vec<(Id, LocalIdx)> = fn_free_vars
                .iter()
                .map(|(id, idx)| (id.clone(), *idx))
                .collect();
            fn_free_vars_sorted.sort_by_key(|(_, idx)| *idx);

            let mut locals: Vec<Id> = fn_free_vars_sorted
                .iter()
                .map(|(id, _)| id.clone())
                .collect();
            locals.extend(sig.params.iter().map(|(id, _)| id.clone()));

            closures.push(Closure {
                idx: closure_idx,
                locals,
                fvs: fn_free_vars_sorted
                    .iter()
                    .map(|(id, use_idx)| ClosureFv {
                        id: id.clone(),
                        alloc_idx: *indices.locals.get(id).unwrap(),
                        use_idx: *use_idx,
                    })
                    .collect(),
                params: sig
                    .params
                    .iter()
                    .map(|(_, ty)| Ty::from_mono_ty(&ty.node))
                    .collect(),
                body,
            });

            // Add free vars of the nested closure that are not defined in the enclosing function as
            // free in the enclosing closure.
            // NB. Use index of the free variable will be different in the nested and enclosing
            // closures!
            for (fv, _) in fn_free_vars {
                if !local_vars.is_bound(&fv) {
                    let local_idx = LocalIdx(free_vars.len() as u32);
                    free_vars.insert(fv, local_idx);
                }
            }

            Expr::ClosureAlloc(closure_idx)
        }
    }
}

fn lower_nl_expr(
    expr: &Named<L<mono::Expr>>,
    closures: &mut Vec<Closure>,
    local_vars: &mut ScopeSet<Id>,
    free_vars: &mut Map<Id, LocalIdx>,
    indices: &mut Indices,
) -> Named<L<Expr>> {
    expr.map_as_ref(|expr| lower_l_expr(expr, closures, local_vars, free_vars, indices))
}

fn lower_l_expr(
    l_expr: &L<mono::Expr>,
    closures: &mut Vec<Closure>,
    local_vars: &mut ScopeSet<Id>,
    free_vars: &mut Map<Id, LocalIdx>,
    indices: &mut Indices,
) -> L<Expr> {
    l_expr
        .map_as_ref(|expr| lower_expr(expr, &l_expr.loc, closures, local_vars, free_vars, indices))
}

fn lower_bl_expr(
    bl_expr: &Box<L<mono::Expr>>,
    closures: &mut Vec<Closure>,
    local_vars: &mut ScopeSet<Id>,
    free_vars: &mut Map<Id, LocalIdx>,
    indices: &mut Indices,
) -> Box<L<Expr>> {
    Box::new(bl_expr.map_as_ref(|expr| {
        lower_expr(expr, &bl_expr.loc, closures, local_vars, free_vars, indices)
    }))
}

fn lower_pat(pat: &mono::Pat, local_vars: &mut ScopeSet<Id>, indices: &mut Indices) -> Pat {
    match pat {
        mono::Pat::Var(var) => {
            let var_idx = LocalIdx(indices.locals.len() as u32);
            indices.locals.insert(var.clone(), var_idx);
            Pat::Var(var_idx)
        }

        mono::Pat::Constr(mono::ConstrPattern {
            constr: mono::Constructor { type_, constr },
            fields,
            ty_args,
        }) => {
            let con_idx: ConIdx = match constr {
                Some(constr) => *indices
                    .sum_cons
                    .get(type_)
                    .unwrap()
                    .get(constr)
                    .unwrap()
                    .get(ty_args)
                    .unwrap(),
                None => *indices
                    .product_cons
                    .get(type_)
                    .unwrap()
                    .get(ty_args)
                    .unwrap(),
            };
            Pat::Constr(ConstrPattern {
                constr: con_idx,
                fields: fields
                    .iter()
                    .map(|named_f| named_f.map_as_ref(|f| lower_l_pat(f, local_vars, indices)))
                    .collect(),
            })
        }

        mono::Pat::Record(fields) => {
            let idx = *indices
                .records
                .get(&RecordShape::from_named_things(fields))
                .unwrap();
            Pat::Record(RecordPattern {
                fields: fields
                    .iter()
                    .map(|field| lower_nl_pat(field, local_vars, indices))
                    .collect(),
                idx,
            })
        }

        mono::Pat::Variant(mono::VariantPattern { constr, fields }) => {
            let idx = *indices
                .variants
                .get(&VariantShape::from_con_and_fields(constr, fields))
                .unwrap();
            Pat::Variant(VariantPattern {
                constr: constr.clone(),
                fields: fields
                    .iter()
                    .map(|field| lower_nl_pat(field, local_vars, indices))
                    .collect(),
                idx,
            })
        }

        mono::Pat::Ignore => Pat::Ignore,

        mono::Pat::Str(str) => Pat::Str(str.clone()),

        mono::Pat::Char(char) => Pat::Char(*char),

        mono::Pat::StrPfx(str, var) => {
            let var_idx = LocalIdx(indices.locals.len() as u32);
            indices.locals.insert(var.clone(), var_idx);
            Pat::StrPfx(str.clone(), var_idx)
        }

        mono::Pat::Or(p1, p2) => Pat::Or(
            Box::new(lower_l_pat(p1, local_vars, indices)),
            Box::new(lower_l_pat(p2, local_vars, indices)),
        ),
    }
}

fn lower_nl_pat(
    pat: &Named<L<mono::Pat>>,
    local_vars: &mut ScopeSet<Id>,
    indices: &mut Indices,
) -> Named<L<Pat>> {
    pat.map_as_ref(|pat| lower_l_pat(pat, local_vars, indices))
}

fn lower_l_pat(pat: &L<mono::Pat>, local_vars: &mut ScopeSet<Id>, indices: &mut Indices) -> L<Pat> {
    pat.map_as_ref(|pat| lower_pat(pat, local_vars, indices))
}

fn lower_source_fun(
    fun: &mono::FunDecl,
    idx: FunIdx,
    ty_args: &Vec<mono::Type>,
    indices: &mut Indices,
    closures: &mut Vec<Closure>,
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

    indices.locals = local_nums;

    let mut local_vars: ScopeSet<Id> = Default::default();
    for (param, _) in &fun.sig.params {
        local_vars.insert(param.clone());
    }

    let body: Vec<L<Stmt>> = fun
        .body
        .as_ref()
        .unwrap()
        .iter()
        .map(|stmt| {
            lower_l_stmt(
                stmt,
                closures,
                &mut local_vars,
                &mut Default::default(), // free vars
                indices,
            )
        })
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

        return_ty: fun
            .sig
            .return_ty
            .as_ref()
            .map(|l| Ty::from_mono_ty(&l.node))
            .unwrap_or(Ty {
                mono_ty: mono::Type::Record { fields: vec![] },
                repr: Repr::U64,
            }),

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
