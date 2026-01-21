//! Numbering pass lowers monomorphic AST to eliminate type arguments. All function and consturctor
//! references are converted into indices by this pass.

pub mod printer;

use crate::ast;
use crate::collections::*;
use crate::mono_ast::{self as mono, Id, L, Loc};
pub(crate) use crate::record_collector::RecordType;
use crate::record_collector::collect_records;
use crate::utils::loc_display;

use smol_str::SmolStr;

#[derive(Debug)]
pub struct LoweredPgm {
    pub heap_objs: Vec<HeapObj>,
    pub funs: Vec<Fun>,
    pub closures: Vec<Closure>,

    /// Maps mono type declarations to their heap object indices.
    ///
    /// Product types will have one index per type. Sum types may have multiple.
    pub type_objs: HashMap<Id, HashMap<Vec<mono::Type>, Vec<HeapObjIdx>>>,

    // Ids of some special cons that the interpreter needs to know.
    //
    // Note that for product types, type and con tags are the same.
    pub true_con_idx: HeapObjIdx,
    pub false_con_idx: HeapObjIdx,
    pub char_con_idx: HeapObjIdx,
    pub ordering_less_con_idx: HeapObjIdx,
    pub ordering_equal_con_idx: HeapObjIdx,
    pub ordering_greater_con_idx: HeapObjIdx,
    pub str_con_idx: HeapObjIdx,
    pub unit_con_idx: HeapObjIdx,
}

pub const CON_CON_IDX: HeapObjIdx = HeapObjIdx(0);
pub const FUN_CON_IDX: HeapObjIdx = HeapObjIdx(1);
pub const CLOSURE_CON_IDX: HeapObjIdx = HeapObjIdx(2);
pub const ARRAY_CON_IDX: HeapObjIdx = HeapObjIdx(3);
const FIRST_FREE_CON_IDX: HeapObjIdx = HeapObjIdx(4);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FunIdx(u32);

impl FunIdx {
    pub fn as_u64(&self) -> u64 {
        u64::from(self.0)
    }

    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HeapObjIdx(pub u32);

impl HeapObjIdx {
    pub fn as_u64(&self) -> u64 {
        u64::from(self.0)
    }

    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LocalIdx(u32);

impl LocalIdx {
    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ClosureIdx(u32);

impl ClosureIdx {
    pub fn as_u64(&self) -> u64 {
        u64::from(self.0)
    }

    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }
}

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
    pub fn from_mono_ty(mono_ty: &mono::Type) -> Repr {
        match mono_ty {
            mono::Type::Named(mono::NamedType { name, args: _ }) => {
                match name.as_str() {
                    "I8" | "U8" => Repr::U8,
                    "I32" | "U32" => Repr::U32,
                    "I64" | "U64" => Repr::U64,
                    _ => Repr::U64, // box
                }
            }

            mono::Type::Record { .. }
            | mono::Type::Variant { .. }
            | mono::Type::Fn(_)
            | mono::Type::Never => Repr::U64,
        }
    }

    pub fn elem_size_in_bytes(&self) -> usize {
        match self {
            Repr::U8 => 1,
            Repr::U32 => 4,
            Repr::U64 => 8,
        }
    }
}

#[derive(Debug)]
pub enum Fun {
    Builtin(BuiltinFunDecl),
    Source(SourceFunDecl),
}

#[derive(Debug, Clone)]
pub enum BuiltinFunDecl {
    Panic,
    PrintStrNoNl,
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
    BitXorU32,
    ToStrI8,
    ToStrU8,
    ToStrI32,
    ToStrU32,
    ToStrU64,
    ToStrI64,
    U8AsI8,
    U8AsU32,
    U32AsU8,
    U32AsI32,
    U32AsU64,
    I8Shl,
    U8Shl,
    I32Shl,
    U32Shl,
    I8Cmp,
    U8Cmp,
    I32Cmp,
    U32Cmp,
    U64Cmp,
    I8Add,
    U8Add,
    I32Add,
    U32Add,
    U64Add,
    I8Sub,
    U8Sub,
    I32Sub,
    U32Sub,
    I8Mul,
    U8Mul,
    I32Mul,
    U32Mul,
    U64Mul,
    I8Div,
    U8Div,
    I32Div,
    U32Div,
    I8Eq,
    U8Eq,
    I32Eq,
    U32Eq,
    U32Mod,
    I8Rem,
    U8Rem,
    I32Rem,
    U32Rem,
    I32AsU32,
    I32Abs,
    I8Neg,
    I32Neg,

    /// `prim throwUnchecked(exn: exn) a / exn?` (`exn?` is implicit)
    ///
    /// This function never throws or returns, so we don't need the exception and return types.
    ThrowUnchecked,

    /// `prim try(cb: Fn() a / exn) Result[exn, a] / exn?` (`exn?` is implicit)
    Try {
        /// Tag of the `Result.Ok` constructor allocated by the `try` on success.
        ok_con: HeapObjIdx,

        //// Tag of the `Result.Err` constructor allocated by the `try` on failure.
        err_con: HeapObjIdx,
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

    ArraySlice {
        t: mono::Type,
    },

    ArrayCopyWithin {
        t: mono::Type,
    },

    ReadFileUtf8,

    GetArgs,
}

#[derive(Debug)]
pub struct SourceFunDecl {
    pub parent_ty: Option<L<Id>>,
    pub name: L<Id>,
    pub idx: FunIdx,
    pub ty_args: Vec<mono::Type>,
    pub locals: Vec<LocalInfo>,
    pub params: Vec<mono::Type>,
    pub return_ty: mono::Type,
    pub exceptions: mono::Type,
    pub body: Vec<L<Stmt>>,
}

#[derive(Debug)]
pub struct LocalInfo {
    pub name: Id,
    pub ty: mono::Type,
}

/// Describes heap allocated objects.
#[derive(Debug)]
pub enum HeapObj {
    Builtin(BuiltinConDecl),
    Source(SourceConDecl),
    Record(RecordType),
}

#[derive(Debug)]
pub enum BuiltinConDecl {
    /// Constructor closure, e.g. `Option.Some`, `Char`.
    ///
    /// Payload holds the constructor index (`ConIdx`).
    ///
    /// Tag of this constructor is `CON_CON_IDX`.
    Con,

    /// Function closure, e.g. `id`, `Vec.withCapacity`.
    ///
    /// Payload holds the function index (`FunIdx`).
    ///
    /// Tag of this constructor is `FUN_CON_IDX`.
    Fun,

    /// A function expression.
    ///
    /// Payload holds the closure index (`ClosureIdx`), then free variables.
    ///
    /// Tag of this constructor is `CLOSURE_CON_IDX`.
    Closure,

    /// For now we have one array constructor. This works currently because all values are 64-bit
    /// wide (so stores are loads are the same for all values) and we don't have GC.
    ///
    /// Tag of this constructor is `ARRAY_CON_IDX`.
    Array,

    // Integers are value types (not boxed), so they don't have tags.
    I8,
    U8,
    I32,
    U32,
    I64,
    U64,
}

#[derive(Debug)]
pub struct SourceConDecl {
    pub name: Id,
    pub idx: HeapObjIdx,
    pub ty_args: Vec<mono::Type>,
    pub fields: Vec<mono::Type>,
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
    /// Local variable.
    LocalVar(LocalIdx),

    /// A function reference.
    Fun(FunIdx),

    /// Constructor closure.
    ///
    /// This allocates a closure that when applied allocates the constructor.
    ///
    /// Note: nullary constructor will be lowered to `ConAlloc`.
    Con(HeapObjIdx),

    /// Constructor allocation.
    ///
    /// The argument list may be empty (for nullary constructors).
    ConAlloc(HeapObjIdx, Vec<L<Expr>>),

    /// Field selection: `<expr>.<id>`.
    FieldSel(FieldSelExpr),

    Call(CallExpr),

    /// Two's complement representation of an integer value, unsigned extended to `u64`.
    Int(u64),

    Str(String),
    BoolAnd(Box<L<Expr>>, Box<L<Expr>>),
    BoolOr(Box<L<Expr>>, Box<L<Expr>>),
    Return(Box<L<Expr>>),
    Match(MatchExpr),
    If(IfExpr),
    ClosureAlloc(ClosureIdx),
    Is(IsExpr),
    Do(Vec<L<Stmt>>),
    Variant(Box<L<Expr>>),
}

#[derive(Debug, Clone)]
pub struct FieldSelExpr {
    pub object: Box<L<Expr>>,

    /// For debugging: name of the field.
    pub field: Id,

    /// Index of the field in the object's payload.
    ///
    /// Note: this is not *offset* of the field from the object's address. E.g. if an object has N
    /// words of header, the field's address will be `object[N + idx]`.
    pub idx: u32,
}

#[derive(Debug, Clone)]
pub struct CallExpr {
    pub fun: Box<L<Expr>>,
    pub args: Vec<L<Expr>>,
}

#[derive(Debug, Clone)]
pub struct MatchExpr {
    pub scrutinee: Box<L<Expr>>,
    pub alts: Vec<Alt>,
}

#[derive(Debug, Clone)]
pub struct Alt {
    pub pat: L<Pat>,
    pub guard: Option<L<Expr>>,
    pub rhs: Vec<L<Stmt>>,
}

#[derive(Debug, Clone)]
pub struct IfExpr {
    pub branches: Vec<(L<Expr>, Vec<L<Stmt>>)>,
    pub else_branch: Option<Vec<L<Stmt>>>,
}

#[derive(Debug, Clone)]
pub struct IsExpr {
    pub expr: Box<L<Expr>>,
    pub pat: L<Pat>,
}

#[derive(Debug, Clone)]
pub enum Pat {
    Var(LocalIdx),
    Con(ConPat),
    Ignore,
    Str(String),
    Char(char),
    Or(Box<L<Pat>>, Box<L<Pat>>),
    Variant(Box<L<Pat>>),
}

#[derive(Debug, Clone)]
pub struct ConPat {
    pub con: HeapObjIdx,
    pub fields: Vec<L<Pat>>,
}

#[derive(Debug)]
pub struct Closure {
    pub idx: ClosureIdx, // for debugging
    pub locals: Vec<LocalInfo>,
    pub fvs: Vec<ClosureFv>,
    pub params: Vec<mono::Type>,
    pub return_ty: mono::Type,
    pub exceptions: mono::Type,
    pub body: Vec<L<Stmt>>,
    pub loc: Loc,
}

/// A free variable in a closure.
#[derive(Debug, Clone)]
pub struct ClosureFv {
    /// Id of the free variable, for debugging.
    pub id: Id,

    /// Index of the local in the closure allocation site.
    pub alloc_idx: LocalIdx,

    /// Index of the local in closure's locals.
    pub use_idx: LocalIdx,
}

////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
struct Indices {
    product_cons: HashMap<Id, HashMap<Vec<mono::Type>, HeapObjIdx>>,
    sum_cons: HashMap<Id, HashMap<Id, HashMap<Vec<mono::Type>, HeapObjIdx>>>,
    funs: HashMap<Id, HashMap<Vec<mono::Type>, FunIdx>>,
    assoc_funs: HashMap<Id, HashMap<Id, HashMap<Vec<mono::Type>, FunIdx>>>,
    records: HashMap<RecordType, HeapObjIdx>,
}

#[derive(Debug, Default)]
pub struct FunScope {
    /// All locals in the function, including captured ones.
    ///
    /// Captured locals will be indexed by their local indices.
    locals: Vec<LocalInfo>,

    /// Indices of captured (free) variables in the function, mapped to their local indices in
    /// `locals`.
    ///
    /// When seeing a free variable, check this map first to see if we've assigned an index to the
    /// free variable before.
    captured_vars: HashMap<Id, ClosureFv>,

    /// Variables bound in the current function.
    ///
    /// This does not include captured (free) variables.
    ///
    /// Any variable that's not here should be captured (free).
    bounds: ScopeMap<Id, LocalIdx>,

    /// When the current function is a closure in another function, this holds the parent function's
    /// scope.
    ///
    /// This is used to look up captured variable info.
    parent_fun_scope: Option<Box<FunScope>>,
}

impl FunScope {
    fn use_var(&mut self, var: &Id, _loc: &Loc) -> LocalIdx {
        // Check if bound.
        if let Some(idx) = self.bounds.get(var) {
            return *idx;
        }

        // Should be bound in parent function. Reuse the index if we already assigned it
        // one.
        match self.captured_vars.get(var) {
            Some(fv) => fv.use_idx,
            None => {
                // Use the variable in the parent function so that the parent function will
                // capture it if it needs to.
                let alloc_idx = self.parent_fun_scope.as_mut().unwrap().use_var(var, _loc);
                let var_ty: mono::Type = self.parent_fun_scope.as_ref().unwrap().locals
                    [alloc_idx.as_usize()]
                .ty
                .clone();

                // Assign new index.
                let use_idx = LocalIdx(self.locals.len() as u32);
                self.locals.push(LocalInfo {
                    name: var.clone(),
                    ty: var_ty,
                });
                self.captured_vars.insert(
                    var.clone(),
                    ClosureFv {
                        id: var.clone(),
                        alloc_idx,
                        use_idx,
                    },
                );
                use_idx
            }
        }
    }
}

pub fn lower(mono_pgm: &mut mono::MonoPgm) -> LoweredPgm {
    // Number all declarations first, then lower the program.
    let mut product_con_nums: HashMap<Id, HashMap<Vec<mono::Type>, HeapObjIdx>> =
        Default::default();
    let mut sum_con_nums: HashMap<Id, HashMap<Id, HashMap<Vec<mono::Type>, HeapObjIdx>>> =
        Default::default();
    let mut fun_nums: HashMap<Id, HashMap<Vec<mono::Type>, FunIdx>> = Default::default();
    let mut assoc_fun_nums: HashMap<Id, HashMap<Id, HashMap<Vec<mono::Type>, FunIdx>>> =
        Default::default();

    // Number type declarations. Start with `FIRST_FREE_CON_IDX`: we have a few constructors that
    // don't have Fir definitions. The first few indices are allocated for them.
    let mut next_con_idx = FIRST_FREE_CON_IDX;
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
                                next_con_idx = HeapObjIdx(next_con_idx.0 + 1);
                                idx
                            });
                    }
                }

                Some(mono::TypeDeclRhs::Product(_)) | None => {
                    if con_id == "Array" {
                        // Skip `Array`: all array types use the same hard-coded index ARRAY_CON_IDX.
                        continue;
                    }
                    product_con_nums
                        .entry(con_id.clone())
                        .or_default()
                        .entry(con_ty_args.clone())
                        .or_insert_with(|| {
                            let idx = next_con_idx;
                            next_con_idx = HeapObjIdx(next_con_idx.0 + 1);
                            idx
                        });
                }
            }
        }
    }

    // Number top-level functions.
    let mut next_fun_idx = FunIdx(0);
    for (fun_id, fun_ty_map) in &mono_pgm.funs {
        for fun_ty_args in fun_ty_map.keys() {
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
            for fun_ty_args in fun_ty_map.keys() {
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
        heap_objs: vec![],
        funs: vec![],
        closures: vec![],
        type_objs: Default::default(),
        true_con_idx: *sum_con_nums
            .get("Bool")
            .unwrap()
            .get("True")
            .unwrap()
            .get(&vec![])
            .unwrap(),
        false_con_idx: *sum_con_nums
            .get("Bool")
            .unwrap()
            .get("False")
            .unwrap()
            .get(&vec![])
            .unwrap(),
        ordering_less_con_idx: *sum_con_nums
            .get("Ordering")
            .unwrap()
            .get("Less")
            .unwrap()
            .get(&vec![])
            .unwrap(),
        ordering_equal_con_idx: *sum_con_nums
            .get("Ordering")
            .unwrap()
            .get("Equal")
            .unwrap()
            .get(&vec![])
            .unwrap(),
        ordering_greater_con_idx: *sum_con_nums
            .get("Ordering")
            .unwrap()
            .get("Greater")
            .unwrap()
            .get(&vec![])
            .unwrap(),
        char_con_idx: *product_con_nums.get("Char").unwrap().get(&vec![]).unwrap(),
        str_con_idx: *product_con_nums.get("Str").unwrap().get(&vec![]).unwrap(),
        unit_con_idx: HeapObjIdx(u32::MAX), // updated below
    };

    // Lower the program. Note that the iteration order here should be the same as above to add
    // right definitions to the right indices in the vectors.

    // Lower types. Add special built-ins first so that they'll have the expected hard-coded
    // indices.
    assert!(lowered_pgm.heap_objs.is_empty());
    lowered_pgm
        .heap_objs
        .push(HeapObj::Builtin(BuiltinConDecl::Con)); // CON_CON_IDX = 0
    lowered_pgm
        .heap_objs
        .push(HeapObj::Builtin(BuiltinConDecl::Fun)); // FUN_CON_IDX = 1
    lowered_pgm
        .heap_objs
        .push(HeapObj::Builtin(BuiltinConDecl::Closure)); // CLOSURE_CON_IDX = 2
    lowered_pgm
        .heap_objs
        .push(HeapObj::Builtin(BuiltinConDecl::Array)); // ARRAY_CON_IDX = 3

    for (con_id, con_ty_map) in &mono_pgm.ty {
        for (con_ty_args, con_decl) in con_ty_map {
            match &con_decl.rhs {
                Some(rhs) => match rhs {
                    mono::TypeDeclRhs::Sum(cons) => {
                        for mono::ConDecl { name, fields } in cons {
                            let idx = HeapObjIdx(lowered_pgm.heap_objs.len() as u32);
                            let name = SmolStr::new(format!("{con_id}_{name}"));
                            lowered_pgm.heap_objs.push(lower_source_con(
                                idx,
                                &name,
                                con_ty_args,
                                fields,
                            ));
                            lowered_pgm
                                .type_objs
                                .entry(con_id.clone())
                                .or_default()
                                .entry(con_ty_args.clone())
                                .or_default()
                                .push(idx);
                        }
                    }

                    mono::TypeDeclRhs::Product(fields) => {
                        let idx = HeapObjIdx(lowered_pgm.heap_objs.len() as u32);
                        lowered_pgm.heap_objs.push(lower_source_con(
                            idx,
                            con_id,
                            con_ty_args,
                            fields,
                        ));
                        lowered_pgm
                            .type_objs
                            .entry(con_id.clone())
                            .or_default()
                            .entry(con_ty_args.clone())
                            .or_default()
                            .push(idx);
                    }
                },

                None => match con_id.as_str() {
                    // Array is handled separately with a hard-coded index (ARRAY_CON_IDX).
                    "Array" => {}

                    "I8" => {
                        assert_eq!(con_ty_args.len(), 0);
                        lowered_pgm
                            .heap_objs
                            .push(HeapObj::Builtin(BuiltinConDecl::I8));
                    }

                    "U8" => {
                        assert_eq!(con_ty_args.len(), 0);
                        lowered_pgm
                            .heap_objs
                            .push(HeapObj::Builtin(BuiltinConDecl::U8));
                    }

                    "I32" => {
                        assert_eq!(con_ty_args.len(), 0);
                        lowered_pgm
                            .heap_objs
                            .push(HeapObj::Builtin(BuiltinConDecl::I32));
                    }

                    "U32" => {
                        assert_eq!(con_ty_args.len(), 0);
                        lowered_pgm
                            .heap_objs
                            .push(HeapObj::Builtin(BuiltinConDecl::U32));
                    }

                    "I64" => {
                        assert_eq!(con_ty_args.len(), 0);
                        lowered_pgm
                            .heap_objs
                            .push(HeapObj::Builtin(BuiltinConDecl::I64));
                    }

                    "U64" => {
                        assert_eq!(con_ty_args.len(), 0);
                        lowered_pgm
                            .heap_objs
                            .push(HeapObj::Builtin(BuiltinConDecl::U64));
                    }

                    other => panic!("Unknown built-in type: {other}"),
                },
            }
        }
    }

    // Assign indices to record shapes.
    let record_shapes = collect_records(mono_pgm);

    // TODO: We could assign indices to records as we see them during lowering below.
    let mut record_indices: HashMap<RecordType, HeapObjIdx> = Default::default();
    for record_shape in record_shapes {
        let idx = next_con_idx;
        next_con_idx = HeapObjIdx(next_con_idx.0 + 1);
        record_indices.insert(record_shape.clone(), idx);
        lowered_pgm.heap_objs.push(HeapObj::Record(record_shape));
    }

    lowered_pgm.unit_con_idx = *record_indices
        .get(&RecordType::unit())
        .unwrap_or_else(|| panic!("BUG: Unit record not defined {record_indices:#?}"));

    let indices = Indices {
        product_cons: product_con_nums,
        sum_cons: sum_con_nums,
        funs: fun_nums,
        assoc_funs: assoc_fun_nums,
        records: record_indices,
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
                    &indices,
                    &mut lowered_pgm.closures,
                    mono_pgm,
                );
                lowered_pgm.funs.push(Fun::Source(source_fun));
            } else {
                match fun_id.as_str() {
                    "printStrNoNl" => {
                        assert_eq!(fun_ty_args.len(), 1); // exception
                        lowered_pgm
                            .funs
                            .push(Fun::Builtin(BuiltinFunDecl::PrintStrNoNl));
                    }

                    "panic" => {
                        // prim panic(msg: Str) a / exn?
                        assert_eq!(fun_ty_args.len(), 2); // a, exn?
                        lowered_pgm.funs.push(Fun::Builtin(BuiltinFunDecl::Panic));
                    }

                    "try" => {
                        // prim try(cb: Fn() a / exn) Result[exn, a] / exn?
                        assert_eq!(fun_ty_args.len(), 3); // a, exn, exn? (implicit)
                        let a = &fun_ty_args[0];
                        let exn = &fun_ty_args[1];
                        let result = indices
                            .sum_cons
                            .get(&SmolStr::new_static("Result"))
                            .unwrap();
                        let ty_args = vec![exn.clone(), a.clone()];
                        let ok_con = *result
                            .get(&SmolStr::new_static("Ok"))
                            .unwrap()
                            .get(&ty_args)
                            .unwrap();
                        let err_con = *result
                            .get(&SmolStr::new_static("Err"))
                            .unwrap()
                            .get(&ty_args)
                            .unwrap();
                        lowered_pgm
                            .funs
                            .push(Fun::Builtin(BuiltinFunDecl::Try { ok_con, err_con }));
                    }

                    "throwUnchecked" => {
                        // prim throwUnchecked(exn: exn) a
                        assert_eq!(fun_ty_args.len(), 3); // exn, a, exn? (implicit)
                        lowered_pgm
                            .funs
                            .push(Fun::Builtin(BuiltinFunDecl::ThrowUnchecked));
                    }

                    "readFileUtf8" => {
                        // prim readFileUtf8(path: Str) Str
                        assert_eq!(fun_ty_args.len(), 1); // exception
                        lowered_pgm
                            .funs
                            .push(Fun::Builtin(BuiltinFunDecl::ReadFileUtf8));
                    }

                    "getArgs" => {
                        // prim getArgs() Array[Str]
                        assert_eq!(fun_ty_args.len(), 1); // exception
                        lowered_pgm.funs.push(Fun::Builtin(BuiltinFunDecl::GetArgs));
                    }

                    other => {
                        panic!("Unknown built-in function: {other} (ty args = {fun_ty_args:?})");
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
                        &indices,
                        &mut lowered_pgm.closures,
                        mono_pgm,
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

                        ("BitXor", "__bitxor") => {
                            assert_eq!(fun_ty_args.len(), 2); // self, exception
                            match &fun_ty_args[0] {
                                mono::Type::Named(mono::NamedType { name, args }) => {
                                    match name.as_str() {
                                        "U32" => {
                                            assert!(args.is_empty());
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::BitXorU32));
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
                                        "U64" => {
                                            assert!(args.is_empty());
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::ToStrU64));
                                        }
                                        "I64" => {
                                            assert!(args.is_empty());
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::ToStrI64));
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

                        ("U32", "asI32") => {
                            assert_eq!(fun_ty_args.len(), 1); // exception
                            lowered_pgm
                                .funs
                                .push(Fun::Builtin(BuiltinFunDecl::U32AsI32));
                        }

                        ("U32", "asU64") => {
                            assert_eq!(fun_ty_args.len(), 1); // exception
                            lowered_pgm
                                .funs
                                .push(Fun::Builtin(BuiltinFunDecl::U32AsU64));
                        }

                        ("U32", "mod") => {
                            assert_eq!(fun_ty_args.len(), 1); // exception
                            lowered_pgm.funs.push(Fun::Builtin(BuiltinFunDecl::U32Mod));
                        }

                        ("U8", "asU32") => {
                            assert_eq!(fun_ty_args.len(), 1); // exception
                            lowered_pgm.funs.push(Fun::Builtin(BuiltinFunDecl::U8AsU32));
                        }

                        ("U8", "asI8") => {
                            assert_eq!(fun_ty_args.len(), 1); // exception
                            lowered_pgm.funs.push(Fun::Builtin(BuiltinFunDecl::U8AsI8));
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

                        ("Rem", "rem") => {
                            assert_eq!(fun_ty_args.len(), 2); // self, exception
                            match &fun_ty_args[0] {
                                mono::Type::Named(mono::NamedType { name, args: _ }) => {
                                    match name.as_str() {
                                        "I8" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::I8Rem));
                                        }

                                        "U8" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::U8Rem));
                                        }

                                        "I32" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::I32Rem));
                                        }

                                        "U32" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::U32Rem));
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

                                        "U64" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::U64Cmp));
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

                                        "U64" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::U64Add));
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

                                        "U64" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::U64Mul));
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
                            // prim Array.new(len: U32) Array[t]
                            assert_eq!(fun_ty_args.len(), 2); // t, exception (implicit)
                            let t = fun_ty_args[0].clone();
                            lowered_pgm
                                .funs
                                .push(Fun::Builtin(BuiltinFunDecl::ArrayNew { t }));
                        }

                        ("Array", "len") => {
                            // prim Array.len(self: Array[t]) U32
                            assert_eq!(fun_ty_args.len(), 2); // t, exception (implicit)
                            // All arrays have the length in the same location, ignore `t`.
                            lowered_pgm
                                .funs
                                .push(Fun::Builtin(BuiltinFunDecl::ArrayLen));
                        }

                        ("Array", "get") => {
                            // prim Array.get(self: Array[t], idx: U32) t
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

                        ("Array", "slice") => {
                            // prim Array.slice(self: Array[t], start: U32, end: U32)
                            assert_eq!(fun_ty_args.len(), 2); // t, exception (implicit)
                            let t = fun_ty_args[0].clone();
                            lowered_pgm
                                .funs
                                .push(Fun::Builtin(BuiltinFunDecl::ArraySlice { t }));
                        }

                        ("Array", "copyWithin") => {
                            // prim Array.copyWithin(self: Array[t], src: U32, dst: U32, len: U32)
                            assert_eq!(fun_ty_args.len(), 2); // t, exception (implicit)
                            let t = fun_ty_args[0].clone();
                            lowered_pgm
                                .funs
                                .push(Fun::Builtin(BuiltinFunDecl::ArrayCopyWithin { t }));
                        }

                        ("I32", "asU32") => {
                            assert_eq!(fun_ty_args.len(), 1); // exception (implicit)
                            lowered_pgm
                                .funs
                                .push(Fun::Builtin(BuiltinFunDecl::I32AsU32));
                        }

                        ("I32", "abs") => {
                            assert_eq!(fun_ty_args.len(), 1); // exception (implicit)
                            lowered_pgm.funs.push(Fun::Builtin(BuiltinFunDecl::I32Abs));
                        }

                        ("Neg", "__neg") => {
                            assert_eq!(fun_ty_args.len(), 2); // t, exception (implicit)
                            match &fun_ty_args[0] {
                                mono::Type::Named(mono::NamedType { name, args: _ }) => {
                                    match name.as_str() {
                                        "I8" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::I8Neg));
                                        }

                                        "I32" => {
                                            lowered_pgm
                                                .funs
                                                .push(Fun::Builtin(BuiltinFunDecl::I32Neg));
                                        }

                                        _ => panic!(),
                                    }
                                }

                                _ => panic!(),
                            }
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
    idx: HeapObjIdx,
    con_id: &SmolStr,
    con_ty_args: &[mono::Type],
    fields: &mono::ConFields,
) -> HeapObj {
    HeapObj::Source(SourceConDecl {
        name: con_id.clone(),
        idx,
        ty_args: con_ty_args.to_vec(),
        fields: match fields {
            mono::ConFields::Empty => vec![],
            mono::ConFields::Named(fields) => fields.values().cloned().collect(),
            mono::ConFields::Unnamed(fields) => fields.to_vec(),
        },
    })
}

fn lower_stmt(
    stmt: &mono::Stmt,
    loc: &ast::Loc,
    closures: &mut Vec<Closure>,
    indices: &Indices,
    scope: &mut FunScope,
    mono_pgm: &mono::MonoPgm,
) -> (Stmt, mono::Type) {
    match stmt {
        mono::Stmt::Let(mono::LetStmt { lhs, rhs }) => {
            let rhs = lower_l_expr(rhs, closures, indices, scope, mono_pgm).0;
            let lhs = lower_l_pat(lhs, indices, scope, mono_pgm, &mut Default::default());
            (Stmt::Let(LetStmt { lhs, rhs }), mono::Type::unit())
        }

        mono::Stmt::Assign(mono::AssignStmt { lhs, rhs }) => (
            Stmt::Assign(AssignStmt {
                lhs: lower_l_expr(lhs, closures, indices, scope, mono_pgm).0,
                rhs: lower_l_expr(rhs, closures, indices, scope, mono_pgm).0,
            }),
            mono::Type::unit(),
        ),

        mono::Stmt::Expr(expr) => {
            let (expr, _expr_vars, expr_ty) =
                lower_expr(expr, loc, closures, indices, scope, mono_pgm);
            (Stmt::Expr(expr), expr_ty)
        }

        mono::Stmt::While(mono::WhileStmt { label, cond, body }) => {
            let (cond, cond_vars, _cond_ty) =
                lower_l_expr(cond, closures, indices, scope, mono_pgm);
            scope.bounds.push_scope(cond_vars);
            let body = body
                .iter()
                .map(|stmt| lower_l_stmt(stmt, closures, indices, scope, mono_pgm).0)
                .collect();
            scope.bounds.exit();
            (
                Stmt::While(WhileStmt {
                    label: label.clone(),
                    cond,
                    body,
                }),
                mono::Type::unit(),
            )
        }

        mono::Stmt::Break { label, level } => (
            Stmt::Break {
                label: label.clone(),
                level: *level,
            },
            mono::Type::Never,
        ),

        mono::Stmt::Continue { label, level } => (
            Stmt::Continue {
                label: label.clone(),
                level: *level,
            },
            mono::Type::Never,
        ),
    }
}

fn lower_l_stmt(
    l_stmt: &L<mono::Stmt>,
    closures: &mut Vec<Closure>,
    indices: &Indices,
    scope: &mut FunScope,
    mono_pgm: &mono::MonoPgm,
) -> (L<Stmt>, mono::Type) {
    let (stmt, stmt_ty) = lower_stmt(
        &l_stmt.node,
        &l_stmt.loc,
        closures,
        indices,
        scope,
        mono_pgm,
    );
    (l_stmt.set_node(stmt), stmt_ty)
}

fn lower_expr(
    expr: &mono::Expr,
    loc: &mono::Loc,
    closures: &mut Vec<Closure>,
    indices: &Indices,
    scope: &mut FunScope,
    mono_pgm: &mono::MonoPgm,
) -> (Expr, HashMap<Id, LocalIdx>, mono::Type) {
    match expr {
        mono::Expr::LocalVar(var) => {
            let local_idx: LocalIdx = scope.use_var(var, loc);
            let local_ty: mono::Type = scope.locals[local_idx.as_usize()].ty.clone();
            (Expr::LocalVar(local_idx), Default::default(), local_ty)
        }

        mono::Expr::TopVar(mono::VarExpr { id, ty_args }) => {
            let fun_idx: FunIdx = *indices.funs.get(id).unwrap().get(ty_args).unwrap();
            let fun_decl: &mono::FunDecl = mono_pgm.funs.get(id).unwrap().get(ty_args).unwrap();
            let fun_ty = fun_decl.sig.ty();
            (
                Expr::Fun(fun_idx),
                Default::default(),
                mono::Type::Fn(fun_ty),
            )
        }

        mono::Expr::ConSel(mono::Con { ty, con, ty_args }) => {
            let ret_ty = mono::Type::Named(mono::NamedType {
                name: ty.clone(),
                args: ty_args.clone(),
            });

            let idx: HeapObjIdx = match con {
                Some(con) => *indices
                    .sum_cons
                    .get(ty)
                    .unwrap()
                    .get(con)
                    .unwrap()
                    .get(ty_args)
                    .unwrap(),
                None => *indices.product_cons.get(ty).unwrap().get(ty_args).unwrap(),
            };

            let ty_decl: &mono::TypeDecl = mono_pgm.ty.get(ty).unwrap().get(ty_args).unwrap();

            let con_fields = match &ty_decl.rhs {
                Some(mono::TypeDeclRhs::Sum(cons)) => 'l: {
                    for con_ in cons {
                        if con_.name == *con.as_ref().unwrap() {
                            break 'l &con_.fields;
                        }
                    }
                    panic!(
                        "BUG: {}: Type {} doesn't have constructor named {}",
                        loc_display(loc),
                        ty,
                        con.as_ref().unwrap()
                    );
                }

                Some(mono::TypeDeclRhs::Product(fields)) => fields,

                None => &mono::ConFields::Empty,
            };

            let con_ty = match con_fields {
                mono::ConFields::Empty => ret_ty,

                mono::ConFields::Named(args) => mono::Type::Fn(mono::FnType {
                    args: mono::FunArgs::Named(
                        args.iter().map(|(k, v)| (k.clone(), v.clone())).collect(),
                    ),
                    ret: Box::new(ret_ty),
                    exn: Box::new(mono::Type::empty()),
                }),

                mono::ConFields::Unnamed(args) => mono::Type::Fn(mono::FnType {
                    args: mono::FunArgs::Positional(args.clone()),
                    ret: Box::new(ret_ty),
                    exn: Box::new(mono::Type::empty()),
                }),
            };

            let expr = if let mono::ConFields::Empty = con_fields {
                Expr::ConAlloc(idx, vec![])
            } else {
                Expr::Con(idx)
            };

            (expr, Default::default(), con_ty)
        }

        mono::Expr::FieldSel(mono::FieldSelExpr { object, field }) => {
            let (object, _object_vars, object_ty) =
                lower_bl_expr(object, closures, indices, scope, mono_pgm);

            let (field_ty, field_idx): (mono::Type, u32) = match object_ty {
                mono::Type::Named(mono::NamedType { name, args }) => {
                    let ty_decl: &mono::TypeDecl =
                        mono_pgm.ty.get(&name).unwrap().get(&args).unwrap();

                    match &ty_decl.rhs {
                        None => {
                            panic!(
                                "BUG: {}: FieldSel object doesn't have fields",
                                loc_display(loc)
                            );
                        }
                        Some(mono::TypeDeclRhs::Sum(_)) => {
                            panic!("BUG: {}: FieldSel object is a sum type", loc_display(loc));
                        }
                        Some(mono::TypeDeclRhs::Product(fields)) => match fields {
                            mono::ConFields::Empty => {
                                panic!(
                                    "BUG: {}: FieldSel object doesn't have fields",
                                    loc_display(loc)
                                );
                            }
                            mono::ConFields::Named(named_fields) => {
                                let mut field_ty: Option<mono::Type> = None;
                                let mut field_idx: u32 = 0;
                                for (field_idx_, (ty_field_name, ty_field_ty)) in
                                    named_fields.iter().enumerate()
                                {
                                    if ty_field_name == field {
                                        field_ty = Some(ty_field_ty.clone());
                                        field_idx = field_idx_ as u32;
                                        break;
                                    }
                                }
                                let field_ty = field_ty.unwrap_or_else(|| {
                                    panic!(
                                        "{}: FieldSel object doesn't have named field",
                                        loc_display(loc)
                                    )
                                });
                                (field_ty, field_idx)
                            }
                            mono::ConFields::Unnamed(_) => {
                                panic!(
                                    "BUG: {}: FieldSel object doesn't have named fields",
                                    loc_display(loc)
                                )
                            }
                        },
                    }
                }

                mono::Type::Record { fields } => {
                    let mut field_ty: Option<mono::Type> = None;
                    let mut field_idx: u32 = 0;
                    for (field_idx_, (record_field_name, record_field_ty)) in
                        fields.iter().enumerate()
                    {
                        if record_field_name == field {
                            field_ty = Some(record_field_ty.clone());
                            field_idx = field_idx_ as u32;
                            break;
                        }
                    }
                    let field_ty = field_ty.unwrap_or_else(|| {
                        panic!(
                            "BUG: {}: FieldSel object with type {} doesn't have the field '{}'",
                            loc_display(loc),
                            mono::Type::Record { fields },
                            field
                        )
                    });
                    (field_ty, field_idx)
                }

                mono::Type::Variant { .. } => {
                    panic!("BUG: {}: FieldSel of variant", loc_display(loc))
                }

                mono::Type::Fn(_) => panic!("BUG: {}: FieldSel of function", loc_display(loc)),

                mono::Type::Never => (mono::Type::Never, 0),
            };

            (
                Expr::FieldSel(FieldSelExpr {
                    object,
                    field: field.clone(),
                    idx: field_idx,
                }),
                Default::default(),
                field_ty,
            )
        }

        mono::Expr::AssocFnSel(mono::AssocFnSelExpr {
            ty,
            member,
            ty_args,
        }) => {
            let fun_idx = *indices
                .assoc_funs
                .get(ty)
                .unwrap()
                .get(member)
                .unwrap()
                .get(ty_args)
                .unwrap();

            let fun_decl: &mono::FunDecl = mono_pgm
                .associated
                .get(ty)
                .unwrap()
                .get(member)
                .unwrap()
                .get(ty_args)
                .unwrap();

            let fun_ty = fun_decl.sig.ty();

            (
                Expr::Fun(fun_idx),
                Default::default(),
                mono::Type::Fn(fun_ty),
            )
        }

        mono::Expr::Call(mono::CallExpr { fun, args }) => {
            let (fun, _fun_vars, fun_ty) = lower_bl_expr(fun, closures, indices, scope, mono_pgm);

            let mono::FnType {
                args: arg_tys,
                ret,
                exn: _,
            } = match fun_ty {
                mono::Type::Fn(fun_ty) => fun_ty,

                mono::Type::Named(_) | mono::Type::Record { .. } | mono::Type::Variant { .. } => {
                    panic!(
                        "BUG: {}: Function in call expression does not have a function type: {}",
                        loc_display(loc),
                        fun_ty,
                    )
                }

                mono::Type::Never => {
                    return (fun.node, Default::default(), mono::Type::Never);
                }
            };

            let expr: Expr = match arg_tys {
                mono::FunArgs::Positional(_) => {
                    let args = args
                        .iter()
                        .map(|mono::CallArg { name: _, expr }| {
                            lower_l_expr(expr, closures, indices, scope, mono_pgm).0
                        })
                        .collect();

                    match &fun.node {
                        Expr::Con(heap_obj_idx) => Expr::ConAlloc(*heap_obj_idx, args),
                        _ => Expr::Call(CallExpr { fun, args }),
                    }
                }

                mono::FunArgs::Named(named_args) => {
                    // Evaluate args in program order, pass in the order expected by the function.
                    let mut arg_locals: HashMap<Id, LocalIdx> = Default::default();

                    for (arg_name, arg_ty) in named_args.iter() {
                        let local_idx = LocalIdx(scope.locals.len() as u32);
                        scope.locals.push(LocalInfo {
                            name: arg_name.clone(),
                            ty: arg_ty.clone(),
                        });
                        let old = arg_locals.insert(arg_name.clone(), local_idx);
                        assert!(old.is_none());
                    }

                    let mut stmts: Vec<L<Stmt>> = Vec::with_capacity(named_args.len());
                    for mono::CallArg { name, expr } in args.iter() {
                        let name = name.as_ref().unwrap();
                        let arg_local = arg_locals.get(name).unwrap();
                        stmts.push(L {
                            node: Stmt::Assign(AssignStmt {
                                lhs: L {
                                    node: Expr::LocalVar(*arg_local),
                                    loc: expr.loc.clone(),
                                },
                                rhs: lower_l_expr(expr, closures, indices, scope, mono_pgm).0,
                            }),
                            loc: expr.loc.clone(),
                        })
                    }

                    let args = named_args
                        .keys()
                        .map(|name| L {
                            node: Expr::LocalVar(*arg_locals.get(name).unwrap()),
                            loc: loc.clone(),
                        })
                        .collect();

                    let call_expr = match &fun.node {
                        Expr::Con(heap_obj_idx) => Expr::ConAlloc(*heap_obj_idx, args),
                        _ => Expr::Call(CallExpr { fun, args }),
                    };

                    stmts.push(L {
                        node: Stmt::Expr(call_expr),
                        loc: loc.clone(),
                    });

                    Expr::Do(stmts)
                }
            };

            (expr, Default::default(), *ret)
        }

        mono::Expr::Int(int) => {
            let kind = int.kind.unwrap();
            let (int_ty_con, value) = match kind {
                ast::IntKind::I8(val) => ("I8", val as u8 as u64),
                ast::IntKind::U8(val) => ("U8", val as u64),
                ast::IntKind::I32(val) => ("I32", val as u32 as u64),
                ast::IntKind::U32(val) => ("U32", val as u64),
                ast::IntKind::I64(val) => ("I64", val as u64),
                ast::IntKind::U64(val) => ("U64", val),
            };
            let ty: mono::Type = mono::Type::Named(mono::NamedType {
                name: SmolStr::new_static(int_ty_con),
                args: vec![],
            });
            (Expr::Int(value), Default::default(), ty)
        }

        mono::Expr::Str(str) => (
            Expr::Str(str.clone()),
            Default::default(),
            mono::Type::Named(mono::NamedType {
                name: SmolStr::new_static("Str"),
                args: vec![],
            }),
        ),

        mono::Expr::Char(char) => (
            Expr::ConAlloc(
                *indices
                    .product_cons
                    .get(&SmolStr::new_static("Char"))
                    .unwrap()
                    .get(&vec![])
                    .unwrap(),
                vec![L {
                    loc: loc.clone(),
                    node: Expr::Int(u64::from(*char as u32)),
                }],
            ),
            Default::default(),
            mono::Type::Named(mono::NamedType {
                name: SmolStr::new_static("Char"),
                args: vec![],
            }),
        ),

        mono::Expr::BinOp(mono::BinOpExpr {
            left,
            right,
            op: mono::BinOp::And,
        }) => {
            let (left, left_vars, _) = lower_bl_expr(left, closures, indices, scope, mono_pgm);
            scope.bounds.push_scope(left_vars);
            let (right, right_vars, _) = lower_bl_expr(right, closures, indices, scope, mono_pgm);
            let mut left_vars = scope.bounds.exit();
            left_vars.extend(right_vars);
            (
                Expr::BoolAnd(left, right),
                left_vars,
                mono::Type::Named(mono::NamedType {
                    name: SmolStr::new_static("Bool"),
                    args: vec![],
                }),
            )
        }

        mono::Expr::BinOp(mono::BinOpExpr {
            left,
            right,
            op: mono::BinOp::Or,
        }) => (
            Expr::BoolOr(
                lower_bl_expr(left, closures, indices, scope, mono_pgm).0,
                lower_bl_expr(right, closures, indices, scope, mono_pgm).0,
            ),
            Default::default(),
            mono::Type::Named(mono::NamedType {
                name: SmolStr::new_static("Bool"),
                args: vec![],
            }),
        ),

        mono::Expr::BinOp(_) => panic!("BUG: {}: Non-desugared BinOp", loc_display(loc)),

        mono::Expr::Record(mono::RecordExpr {
            fields,
            ty: field_tys,
        }) => {
            let record_idx = *indices
                .records
                .get(&RecordType {
                    fields: field_tys.clone(),
                })
                .unwrap();

            // Evaluate args in program order, pass in the order expected by the function.
            let mut arg_locals: HashMap<Id, LocalIdx> = Default::default();

            for (field_name, field_ty) in field_tys.iter() {
                let local_idx = LocalIdx(scope.locals.len() as u32);
                scope.locals.push(LocalInfo {
                    name: field_name.clone(),
                    ty: field_ty.clone(),
                });
                let old = arg_locals.insert(field_name.clone(), local_idx);
                assert!(old.is_none());
            }

            let mut stmts: Vec<L<Stmt>> = Vec::with_capacity(field_tys.len());
            for (name, expr) in fields.iter() {
                let arg_local = arg_locals.get(name).unwrap();
                stmts.push(L {
                    node: Stmt::Assign(AssignStmt {
                        lhs: L {
                            node: Expr::LocalVar(*arg_local),
                            loc: expr.loc.clone(),
                        },
                        rhs: lower_l_expr(expr, closures, indices, scope, mono_pgm).0,
                    }),
                    loc: expr.loc.clone(),
                })
            }

            stmts.push(L {
                node: Stmt::Expr(Expr::ConAlloc(
                    record_idx,
                    field_tys
                        .keys()
                        .map(|name| L {
                            node: Expr::LocalVar(*arg_locals.get(name).unwrap()),
                            loc: loc.clone(),
                        })
                        .collect(),
                )),
                loc: loc.clone(),
            });

            (
                Expr::Do(stmts),
                Default::default(),
                mono::Type::Record {
                    fields: field_tys.clone(),
                },
            )
        }

        mono::Expr::Return(expr) => {
            let (expr, _pat_vars, _expr_ty) =
                lower_bl_expr(expr, closures, indices, scope, mono_pgm);
            (Expr::Return(expr), Default::default(), mono::Type::Never)
        }

        mono::Expr::Match(mono::MatchExpr { scrutinee, alts }) => {
            let (scrutinee, scrut_vars, _scrut_ty) =
                lower_bl_expr(scrutinee, closures, indices, scope, mono_pgm);
            scope.bounds.push_scope(scrut_vars);

            let mut alt_ty: Option<mono::Type> = None;

            let alts = alts
                .iter()
                .map(|mono::Alt { pat, guard, rhs }| {
                    scope.bounds.enter();
                    let pat = lower_l_pat(pat, indices, scope, mono_pgm, &mut Default::default());
                    let guard = guard
                        .as_ref()
                        .map(|guard| lower_l_expr(guard, closures, indices, scope, mono_pgm));
                    if let Some((_guard, guard_vars, _guard_ty)) = guard.as_ref() {
                        scope.bounds.push_scope(guard_vars.clone());
                    }
                    let rhs = rhs
                        .iter()
                        .map(|stmt| {
                            let (stmt, stmt_ty) =
                                lower_l_stmt(stmt, closures, indices, scope, mono_pgm);
                            alt_ty = Some(stmt_ty);
                            stmt
                        })
                        .collect();
                    if guard.is_some() {
                        scope.bounds.exit(); // pop guard's variables
                    }
                    scope.bounds.exit(); // pop pattern's variables
                    Alt {
                        pat,
                        guard: guard.map(|(guard, _guard_vars, _guard_ty)| guard),
                        rhs,
                    }
                })
                .collect();

            scope.bounds.exit(); // pop scrutinee's variables

            (
                Expr::Match(MatchExpr { scrutinee, alts }),
                Default::default(),
                alt_ty.unwrap(),
            )
        }

        mono::Expr::If(mono::IfExpr {
            branches,
            else_branch,
        }) => {
            let mut branch_ty: Option<mono::Type> = None;
            let expr = Expr::If(IfExpr {
                branches: branches
                    .iter()
                    .map(|(cond, rhs)| {
                        let (cond, pat_vars, _cond_ty) =
                            lower_l_expr(cond, closures, indices, scope, mono_pgm);
                        scope.bounds.push_scope(pat_vars);
                        let rhs = rhs
                            .iter()
                            .map(|stmt| {
                                let (stmt, stmt_ty) =
                                    lower_l_stmt(stmt, closures, indices, scope, mono_pgm);
                                branch_ty = Some(stmt_ty);
                                stmt
                            })
                            .collect();
                        scope.bounds.exit();
                        (cond, rhs)
                    })
                    .collect(),
                else_branch: else_branch.as_ref().map(|stmts| {
                    stmts
                        .iter()
                        .map(|stmt| {
                            let (stmt, stmt_ty) =
                                lower_l_stmt(stmt, closures, indices, scope, mono_pgm);
                            branch_ty = Some(stmt_ty);
                            stmt
                        })
                        .collect()
                }),
            });
            (expr, Default::default(), branch_ty.unwrap())
        }

        mono::Expr::Fn(mono::FnExpr { sig, body }) => {
            let parent_fun_scope: FunScope = std::mem::take(scope);

            let mut locals: Vec<LocalInfo> = vec![];
            let mut bounds: ScopeMap<Id, LocalIdx> = Default::default();

            for (param_name, param_ty) in &sig.params {
                let idx = LocalIdx(locals.len() as u32);
                locals.push(LocalInfo {
                    name: param_name.clone(),
                    ty: param_ty.node.clone(),
                });
                bounds.insert(param_name.clone(), idx);
            }

            let mut closure_scope = FunScope {
                locals,
                captured_vars: Default::default(),
                bounds,
                parent_fun_scope: Some(Box::new(parent_fun_scope)),
            };

            let mut fn_local_vars: ScopeSet<Id> = Default::default();
            for (param, _) in &sig.params {
                fn_local_vars.insert(param.clone());
            }

            let body: Vec<L<Stmt>> = body
                .iter()
                .map(|stmt| lower_l_stmt(stmt, closures, indices, &mut closure_scope, mono_pgm).0)
                .collect();

            let closure_idx = ClosureIdx(closures.len() as u32);

            // Restore parent scope.
            *scope = *closure_scope.parent_fun_scope.unwrap();

            let mut fvs: Vec<ClosureFv> = closure_scope.captured_vars.into_values().collect();
            fvs.sort_by_key(|fv| fv.use_idx);

            closures.push(Closure {
                idx: closure_idx,
                locals: closure_scope.locals,
                fvs,
                params: sig.params.iter().map(|(_, ty)| ty.node.clone()).collect(),
                return_ty: sig
                    .return_ty
                    .as_ref()
                    .map(|l| l.node.clone())
                    .unwrap_or(mono::Type::unit()),
                exceptions: sig
                    .exceptions
                    .as_ref()
                    .map(|ty| ty.node.clone())
                    .unwrap_or(mono::Type::empty()),
                body,
                loc: loc.clone(),
            });

            (
                Expr::ClosureAlloc(closure_idx),
                Default::default(),
                mono::Type::Fn(sig.ty()),
            )
        }

        mono::Expr::Is(mono::IsExpr { expr, pat }) => {
            scope.bounds.enter();
            let (expr, _pat_vars_1, _expr_ty) =
                lower_bl_expr(expr, closures, indices, scope, mono_pgm);
            let pat = lower_l_pat(pat, indices, scope, mono_pgm, &mut Default::default());
            let pat_vars_2 = scope.bounds.exit();
            (
                Expr::Is(IsExpr { expr, pat }),
                pat_vars_2,
                mono::Type::Named(mono::NamedType {
                    name: SmolStr::new_static("Bool"),
                    args: vec![],
                }),
            )
        }

        mono::Expr::Do(stmts) => {
            scope.bounds.enter();
            let mut body_ty: Option<mono::Type> = None;
            let expr = Expr::Do(
                stmts
                    .iter()
                    .map(|stmt| {
                        let (stmt, stmt_ty) =
                            lower_l_stmt(stmt, closures, indices, scope, mono_pgm);
                        body_ty = Some(stmt_ty);
                        stmt
                    })
                    .collect(),
            );
            scope.bounds.exit();
            (expr, Default::default(), body_ty.unwrap())
        }

        mono::Expr::Variant(mono::VariantExpr { expr, ty }) => {
            // Note: Type of the expr in the variant won't be a variant type. Use the
            // `VariantExpr`'s type.
            let (expr, vars, _ty) = lower_bl_expr(expr, closures, indices, scope, mono_pgm);
            (
                Expr::Variant(expr),
                vars,
                mono::Type::Variant { alts: ty.clone() },
            )
        }
    }
}

fn lower_l_expr(
    l_expr: &L<mono::Expr>,
    closures: &mut Vec<Closure>,
    indices: &Indices,
    scope: &mut FunScope,
    mono_pgm: &mono::MonoPgm,
) -> (L<Expr>, HashMap<Id, LocalIdx>, mono::Type) {
    let (expr, pat_vars, ty) = lower_expr(
        &l_expr.node,
        &l_expr.loc,
        closures,
        indices,
        scope,
        mono_pgm,
    );
    (
        L {
            loc: l_expr.loc.clone(),
            node: expr,
        },
        pat_vars,
        ty,
    )
}

fn lower_bl_expr(
    bl_expr: &L<mono::Expr>,
    closures: &mut Vec<Closure>,
    indices: &Indices,
    scope: &mut FunScope,
    mono_pgm: &mono::MonoPgm,
) -> (Box<L<Expr>>, HashMap<Id, LocalIdx>, mono::Type) {
    let (expr, pat_vars, ty) = lower_l_expr(bl_expr, closures, indices, scope, mono_pgm);
    (Box::new(expr), pat_vars, ty)
}

fn lower_pat(
    pat: &mono::Pat,
    indices: &Indices,
    scope: &mut FunScope,
    mono_pgm: &mono::MonoPgm,
    loc: &Loc,

    // This map is to map binders in alternatives of or patterns to the same local.
    //
    // Only in or pattern alternatives we allow same binders, so if we see a binder for the second
    // time, we must be checking another alternative of an or pattern.
    mapped_binders: &mut HashMap<Id, LocalIdx>,
) -> Pat {
    match pat {
        mono::Pat::Var(mono::VarPat { var, ty }) => match mapped_binders.get(var) {
            Some(idx) => Pat::Var(*idx),
            None => {
                let var_idx = LocalIdx(scope.locals.len() as u32);
                scope.locals.push(LocalInfo {
                    name: var.clone(),
                    ty: ty.clone(),
                });
                scope.bounds.insert(var.clone(), var_idx);
                mapped_binders.insert(var.clone(), var_idx);
                Pat::Var(var_idx)
            }
        },

        mono::Pat::Con(mono::ConPat {
            con: mono::Con { ty, con, ty_args },
            fields,
        }) => {
            let con_idx: HeapObjIdx = match con {
                Some(con) => *indices
                    .sum_cons
                    .get(ty)
                    .unwrap()
                    .get(con)
                    .unwrap()
                    .get(ty_args)
                    .unwrap(),
                None => *indices.product_cons.get(ty).unwrap().get(ty_args).unwrap(),
            };

            let ty_decl: &mono::TypeDecl = mono_pgm.ty.get(ty).unwrap().get(ty_args).unwrap();

            let con_fields: &mono::ConFields = match &ty_decl.rhs {
                Some(mono::TypeDeclRhs::Sum(cons)) => 'l: {
                    for con_ in cons {
                        if con_.name == *con.as_ref().unwrap() {
                            break 'l &con_.fields;
                        }
                    }
                    panic!(
                        "BUG: {}: Type {} doesn't have constructor named {}",
                        loc_display(loc),
                        ty,
                        con.as_ref().unwrap()
                    );
                }

                Some(mono::TypeDeclRhs::Product(fields)) => fields,

                None => panic!(
                    "BUG: {}: Type {} doesn't have any constructors",
                    loc_display(loc),
                    ty,
                ),
            };

            let field_pats = match con_fields {
                mono::ConFields::Empty => {
                    assert!(fields.is_empty());
                    vec![]
                }

                mono::ConFields::Named(con_fields) => {
                    let mut field_pats: Vec<L<Pat>> = Vec::with_capacity(con_fields.len());

                    for field_name in con_fields.keys() {
                        let pat = match fields.iter().find_map(|field_pat| {
                            if field_pat.name.as_ref().unwrap() == field_name {
                                Some(&field_pat.node)
                            } else {
                                None
                            }
                        }) {
                            Some(pat) => lower_l_pat(pat, indices, scope, mono_pgm, mapped_binders),
                            None => L {
                                node: Pat::Ignore,
                                loc: loc.clone(),
                            },
                        };
                        field_pats.push(pat);
                    }

                    field_pats
                }

                mono::ConFields::Unnamed(con_fields) => {
                    let mut field_pats: Vec<L<Pat>> = fields
                        .iter()
                        .map(|field_pat| {
                            assert!(field_pat.name.is_none());
                            lower_l_pat(&field_pat.node, indices, scope, mono_pgm, mapped_binders)
                        })
                        .collect();

                    for _ in 0..(con_fields.len() - field_pats.len()) {
                        field_pats.push(L {
                            node: Pat::Ignore,
                            loc: loc.clone(),
                        });
                    }

                    field_pats
                }
            };

            Pat::Con(ConPat {
                con: con_idx,
                fields: field_pats,
            })
        }

        mono::Pat::Record(mono::RecordPat { fields, ty }) => {
            let idx = *indices
                .records
                .get(&RecordType { fields: ty.clone() })
                .unwrap();

            let mut field_pats: Vec<L<Pat>> = Vec::with_capacity(ty.len());

            for field_name in ty.keys() {
                let pat = match fields.iter().find_map(|field_pat| {
                    if field_pat.name.as_ref().unwrap() == field_name {
                        Some(&field_pat.node)
                    } else {
                        None
                    }
                }) {
                    Some(pat) => lower_l_pat(pat, indices, scope, mono_pgm, mapped_binders),
                    None => L {
                        node: Pat::Ignore,
                        loc: loc.clone(),
                    },
                };
                field_pats.push(pat);
            }

            Pat::Con(ConPat {
                fields: field_pats,
                con: idx,
            })
        }

        mono::Pat::Ignore => Pat::Ignore,

        mono::Pat::Str(str) => Pat::Str(str.clone()),

        mono::Pat::Char(char) => Pat::Char(*char),

        mono::Pat::Or(p1, p2) => Pat::Or(
            lower_bl_pat(p1, indices, scope, mono_pgm, mapped_binders),
            lower_bl_pat(p2, indices, scope, mono_pgm, mapped_binders),
        ),

        mono::Pat::Variant(mono::VariantPat { pat, ty: _ }) => Pat::Variant(Box::new(lower_l_pat(
            pat,
            indices,
            scope,
            mono_pgm,
            mapped_binders,
        ))),
    }
}

fn lower_bl_pat(
    pat: &L<mono::Pat>,
    indices: &Indices,
    scope: &mut FunScope,
    mono_pgm: &mono::MonoPgm,
    mapped_binders: &mut HashMap<Id, LocalIdx>,
) -> Box<L<Pat>> {
    Box::new(lower_l_pat(pat, indices, scope, mono_pgm, mapped_binders))
}

fn lower_l_pat(
    pat: &L<mono::Pat>,
    indices: &Indices,
    scope: &mut FunScope,
    mono_pgm: &mono::MonoPgm,
    mapped_binders: &mut HashMap<Id, LocalIdx>,
) -> L<Pat> {
    pat.map_as_ref(|pat_| lower_pat(pat_, indices, scope, mono_pgm, &pat.loc, mapped_binders))
}

fn lower_source_fun(
    fun: &mono::FunDecl,
    idx: FunIdx,
    ty_args: &[mono::Type],
    indices: &Indices,
    closures: &mut Vec<Closure>,
    mono_pgm: &mono::MonoPgm,
) -> SourceFunDecl {
    let mut locals: Vec<LocalInfo> = vec![];
    let mut bounds: ScopeMap<Id, LocalIdx> = Default::default();
    let mut params: Vec<mono::Type> = vec![];

    for (param, ty) in &fun.sig.params {
        bounds.insert(param.clone(), LocalIdx(locals.len() as u32));
        locals.push(LocalInfo {
            name: param.clone(),
            ty: ty.node.clone(),
        });
    }

    let mut scope = FunScope {
        locals,
        captured_vars: Default::default(),
        bounds,
        parent_fun_scope: None,
    };

    let body: Vec<L<Stmt>> = fun
        .body
        .as_ref()
        .unwrap()
        .iter()
        .map(|stmt| lower_l_stmt(stmt, closures, indices, &mut scope, mono_pgm).0)
        .collect();

    params.extend(
        fun.sig
            .params
            .iter()
            .map(|(_, param_ty)| param_ty.node.clone()),
    );

    SourceFunDecl {
        parent_ty: fun.parent_ty.clone(),
        name: fun.name.clone(),
        idx,
        ty_args: ty_args.to_vec(),
        locals: scope.locals,
        body,
        params,

        return_ty: fun
            .sig
            .return_ty
            .as_ref()
            .map(|l| l.node.clone())
            .unwrap_or(mono::Type::unit()),

        // Constructors don't have exception types as they cannot throw, and their type parameters
        // need to be the same as the constructed type's type parameters. We can assume their
        // exception type to be empty type (variant with no constructor).
        exceptions: fun
            .sig
            .exceptions
            .as_ref()
            .map(|ty| ty.node.clone())
            .unwrap_or(mono::Type::empty()),
    }
}
