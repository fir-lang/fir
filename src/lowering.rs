//! Numbering pass lowers monomorphic AST to eliminate type arguments. All function and consturctor
//! references are converted into indices by this pass.

pub mod printer;

use crate::ast;
use crate::collections::*;
use crate::mono_ast::{self as mono, Id, L, Loc};
use crate::type_collector::collect_anonymous_types;
pub(crate) use crate::type_collector::{RecordType, VariantType};
use crate::utils::loc_display;

use smol_str::SmolStr;

#[derive(Debug)]
pub struct LoweredPgm {
    pub heap_objs: Vec<HeapObj>,
    pub funs: Vec<Fun>,
    pub closures: Vec<Closure>,

    pub named_tys: HashMap<Id, HashMap<Vec<mono::Type>, TypeIdx>>,
    pub record_tys: HashMap<RecordType, TypeIdx>,
    pub variant_tys: HashMap<VariantType, TypeIdx>,

    /// Indexed by `TypeIdx`.
    pub types: Vec<TypeDecl>,

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
    pub array_u8_con_idx: HeapObjIdx,
    pub array_u64_con_idx: HeapObjIdx,

    // To be able to allocate `Array[Str]` in `prim getArgs() Array[Str]`.
    //
    // This is optional as not all programs will use `getArgs`. If a program uses `getArgs`,
    // `Array[Str]` will also be compiled, so this will always be available.
    pub array_str_con_idx: Option<HeapObjIdx>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeIdx(pub u32);

impl TypeIdx {
    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug)]
pub enum TypeDecl {
    Named(NamedTypeDecl),
    Record(RecordType, HeapObjIdx),
    Variant(VariantType),
}

#[derive(Debug)]
pub struct NamedTypeDecl {
    pub name: Id,
    pub ty_args: Vec<mono::Type>,
    pub rhs: NamedTypeRhs,
    pub con_indices: Vec<HeapObjIdx>,
    pub sum: bool,
    pub value: bool,
}

#[derive(Debug)]
pub enum NamedTypeRhs {
    Source(mono::TypeDeclRhs),
    Builtin(BuiltinConDecl, HeapObjIdx),
}

pub const CON_CON_IDX: HeapObjIdx = HeapObjIdx(0);
pub const FUN_CON_IDX: HeapObjIdx = HeapObjIdx(1);
pub const CLOSURE_CON_IDX: HeapObjIdx = HeapObjIdx(2);
const FIRST_FREE_CON_IDX: HeapObjIdx = HeapObjIdx(3);

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

            mono::Type::Record { .. } | mono::Type::Variant { .. } | mono::Type::Fn(_) => Repr::U64,
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
pub struct Fun {
    pub parent_ty: Option<L<Id>>,
    pub name: L<Id>,
    pub idx: FunIdx,
    pub ty_args: Vec<mono::Type>,
    pub params: Vec<mono::Type>,
    pub return_ty: mono::Type,
    pub exceptions: mono::Type,
    pub body: FunBody,
}

#[derive(Debug)]
pub enum FunBody {
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
        con_idx: HeapObjIdx,
    },

    ArrayLen {
        t: mono::Type,
    },

    ArrayGet {
        t: mono::Type,
    },

    ArraySet {
        t: mono::Type,
    },

    ArraySlice {
        t: mono::Type,
        con_idx: HeapObjIdx,
    },

    ArrayCopyWithin {
        t: mono::Type,
    },

    ReadFileUtf8,

    GetArgs,
}

#[derive(Debug)]
pub struct SourceFunDecl {
    pub locals: Vec<LocalInfo>,
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
    Variant(VariantType),
}

#[derive(Debug, Clone)]
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

    Array {
        t: mono::Type,
    },

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
    pub rhs_ty: mono::Type,
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
    ConAlloc {
        con_idx: HeapObjIdx,
        args: Vec<L<Expr>>,
        arg_tys: Vec<mono::Type>,
        ret_ty: mono::Type,
    },

    /// Field selection: `<expr>.<id>`.
    FieldSel(FieldSelExpr),

    Call(CallExpr),

    /// Two's complement representation of an integer value, unsigned extended to `u64`.
    Int(u64),

    Str(String),

    BoolAnd(Box<L<Expr>>, Box<L<Expr>>),

    BoolOr(Box<L<Expr>>, Box<L<Expr>>),

    Return(
        /// The returned expression.
        Box<L<Expr>>,
        /// Type of the `return` expression.
        ///
        /// Note: this is not the the type of the returned expression!
        mono::Type,
    ),

    Match(MatchExpr),

    If(IfExpr),

    ClosureAlloc(ClosureIdx),

    Is(IsExpr),

    Do(
        Vec<L<Stmt>>,
        /// Type of the whole expression.
        mono::Type,
    ),

    Variant {
        expr: Box<L<Expr>>,
        expr_ty: mono::Type,
        variant_ty: OrdMap<Id, mono::NamedType>,
    },
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

    pub object_ty: mono::Type,
}

#[derive(Debug, Clone)]
pub struct CallExpr {
    pub fun: Box<L<Expr>>,
    pub args: Vec<L<Expr>>,
    pub fun_ty: mono::FnType,
}

#[derive(Debug, Clone)]
pub struct MatchExpr {
    pub scrutinee: Box<L<Expr>>,
    pub alts: Vec<Alt>,
    pub scrut_ty: mono::Type,
    pub ty: mono::Type,
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
    pub ty: mono::Type,
}

#[derive(Debug, Clone)]
pub struct IsExpr {
    pub expr: Box<L<Expr>>,
    pub pat: L<Pat>,
    pub expr_ty: mono::Type,
}

#[derive(Debug, Clone)]
pub enum Pat {
    Var(VarPat),
    Con(ConPat),
    Ignore,
    Str(String),
    Char(char),
    Or(Box<L<Pat>>, Box<L<Pat>>),
    Variant {
        pat: Box<L<Pat>>,
        variant_ty: OrdMap<Id, mono::NamedType>,
        pat_ty: mono::Type,
    },
}

#[derive(Debug, Clone)]
pub struct VarPat {
    pub idx: LocalIdx,

    /// When the binder was refined by pattern matching, the local in `SourceFunDecl` will have the
    /// refined type, and this will be the original type.
    ///
    /// When pattern matching, we should convert the original type to the local's type.
    pub original_ty: mono::Type,
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
        named_tys: Default::default(),
        record_tys: Default::default(),
        variant_tys: Default::default(),
        types: vec![],
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
        array_u8_con_idx: *product_con_nums
            .get("Array")
            .unwrap()
            .get(&vec![mono::Type::u8()])
            .unwrap(),
        array_u64_con_idx: *product_con_nums
            .get("Array")
            .unwrap()
            .get(&vec![mono::Type::u64()])
            .unwrap(),
        array_str_con_idx: product_con_nums
            .get("Array")
            .and_then(|ty_map| ty_map.get(&vec![mono::Type::str()]))
            .copied(),
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

    for (con_id, con_ty_map) in &mono_pgm.ty {
        for (con_ty_args, con_decl) in con_ty_map {
            let mut con_indices: Vec<HeapObjIdx> = vec![];
            let mut sum = false;
            let rhs: NamedTypeRhs = match &con_decl.rhs {
                Some(rhs) => {
                    match rhs {
                        mono::TypeDeclRhs::Sum(cons) => {
                            sum = true;
                            // For sum types, we generate an index representing the type itself (rather
                            // than its consturctors). This index is used in dependency anlaysis, and to
                            // get the type details during code generation.
                            for mono::ConDecl { name, fields } in cons {
                                let idx = HeapObjIdx(lowered_pgm.heap_objs.len() as u32);
                                let name = SmolStr::new(format!("{con_id}_{name}"));
                                lowered_pgm.heap_objs.push(lower_source_con(
                                    idx,
                                    &name,
                                    con_ty_args,
                                    fields,
                                ));
                                con_indices.push(idx);
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
                            con_indices.push(idx);
                        }
                    }
                    NamedTypeRhs::Source(rhs.clone())
                }

                None => {
                    let con = match con_id.as_str() {
                        "Array" => {
                            assert_eq!(con_ty_args.len(), 1);
                            BuiltinConDecl::Array {
                                t: con_ty_args[0].clone(),
                            }
                        }

                        "I8" => {
                            assert_eq!(con_ty_args.len(), 0);
                            BuiltinConDecl::I8
                        }

                        "U8" => {
                            assert_eq!(con_ty_args.len(), 0);
                            BuiltinConDecl::U8
                        }

                        "I32" => {
                            assert_eq!(con_ty_args.len(), 0);
                            BuiltinConDecl::I32
                        }

                        "U32" => {
                            assert_eq!(con_ty_args.len(), 0);
                            BuiltinConDecl::U32
                        }

                        "I64" => {
                            assert_eq!(con_ty_args.len(), 0);
                            BuiltinConDecl::I64
                        }

                        "U64" => {
                            assert_eq!(con_ty_args.len(), 0);
                            BuiltinConDecl::U64
                        }

                        other => panic!("Unknown built-in type: {other}"),
                    };

                    let idx = HeapObjIdx(lowered_pgm.heap_objs.len() as u32);
                    lowered_pgm.heap_objs.push(HeapObj::Builtin(con.clone()));
                    con_indices.push(idx);
                    NamedTypeRhs::Builtin(con, idx)
                }
            };

            let ty_idx = TypeIdx(lowered_pgm.types.len() as u32);
            lowered_pgm
                .named_tys
                .entry(con_id.clone())
                .or_default()
                .insert(con_ty_args.clone(), ty_idx);
            lowered_pgm.types.push(TypeDecl::Named(NamedTypeDecl {
                name: con_id.clone(),
                ty_args: con_ty_args.clone(),
                rhs,
                con_indices,
                sum,
                value: con_decl.value,
            }));
        }
    }

    // Assign indices to record shapes.
    let (record_types, variant_types) = collect_anonymous_types(mono_pgm);

    let mut record_indices: HashMap<RecordType, HeapObjIdx> = Default::default();
    for record_type in record_types {
        let idx = next_con_idx;
        next_con_idx = HeapObjIdx(next_con_idx.0 + 1);
        record_indices.insert(record_type.clone(), idx);
        lowered_pgm
            .heap_objs
            .push(HeapObj::Record(record_type.clone()));
        let ty_idx = TypeIdx(lowered_pgm.types.len() as u32);
        lowered_pgm.record_tys.insert(record_type.clone(), ty_idx);
        lowered_pgm.types.push(TypeDecl::Record(record_type, idx));
    }

    let mut variant_indices: HashMap<VariantType, HeapObjIdx> = Default::default();
    for variant_type in variant_types {
        let idx = next_con_idx;
        next_con_idx = HeapObjIdx(next_con_idx.0 + 1);
        variant_indices.insert(variant_type.clone(), idx);
        lowered_pgm
            .heap_objs
            .push(HeapObj::Variant(variant_type.clone()));
        let ty_idx = TypeIdx(lowered_pgm.types.len() as u32);
        lowered_pgm.variant_tys.insert(variant_type.clone(), ty_idx);
        lowered_pgm.types.push(TypeDecl::Variant(variant_type));
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
            let body = match &fun_decl.body {
                Some(body) => FunBody::Source(lower_source_fun(
                    &fun_decl.sig,
                    body,
                    &indices,
                    &mut lowered_pgm.closures,
                    mono_pgm,
                )),
                None => {
                    FunBody::Builtin(match fun_id.as_str() {
                        "printStrNoNl" => {
                            assert_eq!(fun_ty_args.len(), 1); // exception
                            BuiltinFunDecl::PrintStrNoNl
                        }

                        "panic" => {
                            // prim panic(msg: Str) a / exn?
                            assert_eq!(fun_ty_args.len(), 2); // a, exn?
                            BuiltinFunDecl::Panic
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
                            BuiltinFunDecl::Try { ok_con, err_con }
                        }

                        "throwUnchecked" => {
                            // prim throwUnchecked(exn: exn) a
                            assert_eq!(fun_ty_args.len(), 3); // exn, a, exn? (implicit)
                            BuiltinFunDecl::ThrowUnchecked
                        }

                        "readFileUtf8" => {
                            // prim readFileUtf8(path: Str) Str
                            assert_eq!(fun_ty_args.len(), 1); // exception
                            BuiltinFunDecl::ReadFileUtf8
                        }

                        "getArgs" => {
                            // prim getArgs() Array[Str]
                            assert_eq!(fun_ty_args.len(), 1); // exception
                            BuiltinFunDecl::GetArgs
                        }

                        other => {
                            panic!(
                                "Unknown built-in function: {other} (ty args = {fun_ty_args:?})"
                            );
                        }
                    })
                }
            };
            lowered_pgm.funs.push(Fun {
                parent_ty: None,
                name: fun_decl.name.clone(),
                idx,
                ty_args: fun_ty_args.clone(),
                params: fun_decl
                    .sig
                    .params
                    .iter()
                    .map(|(_, ty)| ty.node.clone())
                    .collect(),
                return_ty: fun_decl
                    .sig
                    .return_ty
                    .as_ref()
                    .map(|l| l.node.clone())
                    .unwrap_or(mono::Type::unit()),
                exceptions: fun_decl
                    .sig
                    .exceptions
                    .as_ref()
                    .map(|l| l.node.clone())
                    .unwrap_or(mono::Type::unit()),
                body,
            });
        }
    }

    // Lower associated functions.
    for (ty, assoc_fun_map) in &mono_pgm.associated {
        for (fun, fun_ty_map) in assoc_fun_map {
            for (fun_ty_args, fun_decl) in fun_ty_map {
                let idx = FunIdx(lowered_pgm.funs.len() as u32);
                let body = match &fun_decl.body {
                    Some(body) => FunBody::Source(lower_source_fun(
                        &fun_decl.sig,
                        body,
                        &indices,
                        &mut lowered_pgm.closures,
                        mono_pgm,
                    )),
                    None => {
                        FunBody::Builtin(match (ty.as_str(), fun.as_str()) {
                            ("Shr", "__shr") => {
                                assert_eq!(fun_ty_args.len(), 2); // self, exception
                                match &fun_ty_args[0] {
                                    mono::Type::Named(mono::NamedType { name, args }) => {
                                        match name.as_str() {
                                            "I8" => {
                                                assert!(args.is_empty());
                                                BuiltinFunDecl::ShrI8
                                            }
                                            "U8" => {
                                                assert!(args.is_empty());
                                                BuiltinFunDecl::ShrU8
                                            }
                                            "I32" => {
                                                assert!(args.is_empty());
                                                BuiltinFunDecl::ShrI32
                                            }
                                            "U32" => {
                                                assert!(args.is_empty());
                                                BuiltinFunDecl::ShrU32
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
                                                BuiltinFunDecl::BitAndI8
                                            }
                                            "U8" => {
                                                assert!(args.is_empty());
                                                BuiltinFunDecl::BitAndU8
                                            }
                                            "I32" => {
                                                assert!(args.is_empty());
                                                BuiltinFunDecl::BitAndI32
                                            }
                                            "U32" => {
                                                assert!(args.is_empty());
                                                BuiltinFunDecl::BitAndU32
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
                                                BuiltinFunDecl::BitOrI8
                                            }
                                            "U8" => {
                                                assert!(args.is_empty());
                                                BuiltinFunDecl::BitOrU8
                                            }
                                            "I32" => {
                                                assert!(args.is_empty());
                                                BuiltinFunDecl::BitOrI32
                                            }
                                            "U32" => {
                                                assert!(args.is_empty());
                                                BuiltinFunDecl::BitOrU32
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
                                                BuiltinFunDecl::BitXorU32
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
                                                BuiltinFunDecl::ToStrI8
                                            }
                                            "U8" => {
                                                assert!(args.is_empty());
                                                BuiltinFunDecl::ToStrU8
                                            }
                                            "I32" => {
                                                assert!(args.is_empty());
                                                BuiltinFunDecl::ToStrI32
                                            }
                                            "U32" => {
                                                assert!(args.is_empty());
                                                BuiltinFunDecl::ToStrU32
                                            }
                                            "U64" => {
                                                assert!(args.is_empty());
                                                BuiltinFunDecl::ToStrU64
                                            }
                                            "I64" => {
                                                assert!(args.is_empty());
                                                BuiltinFunDecl::ToStrI64
                                            }
                                            _ => panic!(),
                                        }
                                    }
                                    _ => panic!(),
                                }
                            }

                            ("U32", "asU8") => {
                                assert_eq!(fun_ty_args.len(), 1); // exception
                                BuiltinFunDecl::U32AsU8
                            }

                            ("U32", "asI32") => {
                                assert_eq!(fun_ty_args.len(), 1); // exception
                                BuiltinFunDecl::U32AsI32
                            }

                            ("U32", "asU64") => {
                                assert_eq!(fun_ty_args.len(), 1); // exception
                                BuiltinFunDecl::U32AsU64
                            }

                            ("U32", "mod") => {
                                assert_eq!(fun_ty_args.len(), 1); // exception
                                BuiltinFunDecl::U32Mod
                            }

                            ("U8", "asU32") => {
                                assert_eq!(fun_ty_args.len(), 1); // exception
                                BuiltinFunDecl::U8AsU32
                            }

                            ("U8", "asI8") => {
                                assert_eq!(fun_ty_args.len(), 1); // exception
                                BuiltinFunDecl::U8AsI8
                            }

                            ("Shl", "__shl") => {
                                assert_eq!(fun_ty_args.len(), 2); // self, exception
                                match &fun_ty_args[0] {
                                    mono::Type::Named(mono::NamedType { name, args: _ }) => {
                                        match name.as_str() {
                                            "I8" => BuiltinFunDecl::I8Shl,
                                            "U8" => BuiltinFunDecl::U8Shl,
                                            "I32" => BuiltinFunDecl::I32Shl,
                                            "U32" => BuiltinFunDecl::U32Shl,
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
                                            "I8" => BuiltinFunDecl::I8Rem,
                                            "U8" => BuiltinFunDecl::U8Rem,
                                            "I32" => BuiltinFunDecl::I32Rem,
                                            "U32" => BuiltinFunDecl::U32Rem,
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
                                            "I8" => BuiltinFunDecl::I8Cmp,
                                            "U8" => BuiltinFunDecl::U8Cmp,
                                            "I32" => BuiltinFunDecl::I32Cmp,
                                            "U32" => BuiltinFunDecl::U32Cmp,
                                            "U64" => BuiltinFunDecl::U64Cmp,
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
                                            "I8" => BuiltinFunDecl::I8Add,
                                            "U8" => BuiltinFunDecl::U8Add,
                                            "I32" => BuiltinFunDecl::I32Add,
                                            "U32" => BuiltinFunDecl::U32Add,
                                            "U64" => BuiltinFunDecl::U64Add,
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
                                            "I8" => BuiltinFunDecl::I8Sub,
                                            "U8" => BuiltinFunDecl::U8Sub,
                                            "I32" => BuiltinFunDecl::I32Sub,
                                            "U32" => BuiltinFunDecl::U32Sub,
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
                                            "I8" => BuiltinFunDecl::I8Mul,
                                            "U8" => BuiltinFunDecl::U8Mul,
                                            "I32" => BuiltinFunDecl::I32Mul,
                                            "U32" => BuiltinFunDecl::U32Mul,
                                            "U64" => BuiltinFunDecl::U64Mul,

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
                                            "I8" => BuiltinFunDecl::I8Div,
                                            "U8" => BuiltinFunDecl::U8Div,
                                            "I32" => BuiltinFunDecl::I32Div,
                                            "U32" => BuiltinFunDecl::U32Div,
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
                                            "I8" => BuiltinFunDecl::I8Eq,
                                            "U8" => BuiltinFunDecl::U8Eq,
                                            "I32" => BuiltinFunDecl::I32Eq,
                                            "U32" => BuiltinFunDecl::U32Eq,
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
                                let con_idx = *indices
                                    .product_cons
                                    .get("Array")
                                    .unwrap()
                                    .get(&vec![t.clone()])
                                    .unwrap();
                                BuiltinFunDecl::ArrayNew { t, con_idx }
                            }

                            ("Array", "len") => {
                                // prim Array.len(self: Array[t]) U32
                                assert_eq!(fun_ty_args.len(), 2); // t, exception (implicit)
                                let t = fun_ty_args[0].clone();
                                BuiltinFunDecl::ArrayLen { t }
                            }

                            ("Array", "get") => {
                                // prim Array.get(self: Array[t], idx: U32) t
                                assert_eq!(fun_ty_args.len(), 2); // t, exception (implicit)
                                let t = fun_ty_args[0].clone();
                                BuiltinFunDecl::ArrayGet { t }
                            }

                            ("Array", "set") => {
                                // prim Array.set(self: Array[t], idx: U32, elem: t)
                                assert_eq!(fun_ty_args.len(), 2); // t, exception (implicit)
                                let t = fun_ty_args[0].clone();
                                BuiltinFunDecl::ArraySet { t }
                            }

                            ("Array", "slice") => {
                                // prim Array.slice(self: Array[t], start: U32, end: U32)
                                assert_eq!(fun_ty_args.len(), 2); // t, exception (implicit)
                                let t = fun_ty_args[0].clone();
                                let con_idx = *indices
                                    .product_cons
                                    .get("Array")
                                    .unwrap()
                                    .get(&vec![t.clone()])
                                    .unwrap();
                                BuiltinFunDecl::ArraySlice { t, con_idx }
                            }

                            ("Array", "copyWithin") => {
                                // prim Array.copyWithin(self: Array[t], src: U32, dst: U32, len: U32)
                                assert_eq!(fun_ty_args.len(), 2); // t, exception (implicit)
                                let t = fun_ty_args[0].clone();
                                BuiltinFunDecl::ArrayCopyWithin { t }
                            }

                            ("I32", "asU32") => {
                                assert_eq!(fun_ty_args.len(), 1); // exception (implicit)
                                BuiltinFunDecl::I32AsU32
                            }

                            ("I32", "abs") => {
                                assert_eq!(fun_ty_args.len(), 1); // exception (implicit)
                                BuiltinFunDecl::I32Abs
                            }

                            ("Neg", "__neg") => {
                                assert_eq!(fun_ty_args.len(), 2); // t, exception (implicit)
                                match &fun_ty_args[0] {
                                    mono::Type::Named(mono::NamedType { name, args: _ }) => {
                                        match name.as_str() {
                                            "I8" => BuiltinFunDecl::I8Neg,
                                            "I32" => BuiltinFunDecl::I32Neg,
                                            _ => panic!(),
                                        }
                                    }

                                    _ => panic!(),
                                }
                            }

                            (_, _) => todo!("Built-in function {}.{}", ty, fun),
                        })
                    }
                };
                lowered_pgm.funs.push(Fun {
                    parent_ty: None,
                    name: fun_decl.name.clone(),
                    idx,
                    ty_args: fun_ty_args.clone(),
                    params: fun_decl
                        .sig
                        .params
                        .iter()
                        .map(|(_, ty)| ty.node.clone())
                        .collect(),
                    return_ty: fun_decl
                        .sig
                        .return_ty
                        .as_ref()
                        .map(|l| l.node.clone())
                        .unwrap_or(mono::Type::unit()),
                    exceptions: fun_decl
                        .sig
                        .exceptions
                        .as_ref()
                        .map(|l| l.node.clone())
                        .unwrap_or(mono::Type::unit()),
                    body,
                });
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
) -> Stmt {
    match stmt {
        mono::Stmt::Let(mono::LetStmt { lhs, rhs }) => {
            let rhs_ty = rhs.node.ty();
            let (rhs, _) = lower_l_expr(rhs, closures, indices, scope, mono_pgm);
            let lhs = lower_l_pat(lhs, indices, scope, mono_pgm, &mut Default::default());
            Stmt::Let(LetStmt { lhs, rhs, rhs_ty })
        }

        mono::Stmt::Assign(mono::AssignStmt { lhs, rhs }) => Stmt::Assign(AssignStmt {
            lhs: lower_l_expr(lhs, closures, indices, scope, mono_pgm).0,
            rhs: lower_l_expr(rhs, closures, indices, scope, mono_pgm).0,
        }),

        mono::Stmt::Expr(expr) => {
            let (expr, _expr_vars) = lower_expr(expr, loc, closures, indices, scope, mono_pgm);
            Stmt::Expr(expr)
        }

        mono::Stmt::While(mono::WhileStmt { label, cond, body }) => {
            let (cond, cond_vars) = lower_l_expr(cond, closures, indices, scope, mono_pgm);
            scope.bounds.push_scope(cond_vars);
            let body = body
                .iter()
                .map(|stmt| lower_l_stmt(stmt, closures, indices, scope, mono_pgm))
                .collect();
            scope.bounds.exit();
            Stmt::While(WhileStmt {
                label: label.clone(),
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
    l_stmt: &L<mono::Stmt>,
    closures: &mut Vec<Closure>,
    indices: &Indices,
    scope: &mut FunScope,
    mono_pgm: &mono::MonoPgm,
) -> L<Stmt> {
    let stmt = lower_stmt(
        &l_stmt.node,
        &l_stmt.loc,
        closures,
        indices,
        scope,
        mono_pgm,
    );
    l_stmt.set_node(stmt)
}

fn lower_expr(
    expr: &mono::Expr,
    loc: &mono::Loc,
    closures: &mut Vec<Closure>,
    indices: &Indices,
    scope: &mut FunScope,
    mono_pgm: &mono::MonoPgm,
) -> (Expr, HashMap<Id, LocalIdx>) {
    match expr {
        mono::Expr::LocalVar(var, _) => {
            let local_idx: LocalIdx = scope.use_var(var, loc);
            (Expr::LocalVar(local_idx), Default::default())
        }

        mono::Expr::TopVar(mono::VarExpr { id, ty_args, ty: _ }) => {
            let fun_idx: FunIdx = *indices.funs.get(id).unwrap().get(ty_args).unwrap();
            (Expr::Fun(fun_idx), Default::default())
        }

        mono::Expr::ConSel(mono::Con {
            ty_id,
            con,
            ty_args,
            ty,
        }) => {
            let idx: HeapObjIdx = match con {
                Some(con) => *indices
                    .sum_cons
                    .get(ty_id)
                    .unwrap()
                    .get(con)
                    .unwrap()
                    .get(ty_args)
                    .unwrap(),
                None => *indices
                    .product_cons
                    .get(ty_id)
                    .unwrap()
                    .get(ty_args)
                    .unwrap(),
            };

            let ty_decl: &mono::TypeDecl = mono_pgm.ty.get(ty_id).unwrap().get(ty_args).unwrap();

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
                        ty_id,
                        con.as_ref().unwrap()
                    );
                }

                Some(mono::TypeDeclRhs::Product(fields)) => fields,

                None => &mono::ConFields::Empty,
            };

            let expr = if let mono::ConFields::Empty = con_fields {
                Expr::ConAlloc {
                    con_idx: idx,
                    args: vec![],
                    arg_tys: vec![],
                    ret_ty: ty.clone(),
                }
            } else {
                Expr::Con(idx)
            };

            (expr, Default::default())
        }

        mono::Expr::FieldSel(mono::FieldSelExpr {
            object,
            field,
            ty: _,
        }) => {
            let object_ty = object.node.ty();

            let (object, _object_vars) = lower_bl_expr(object, closures, indices, scope, mono_pgm);

            let field_idx: u32 = match &object_ty {
                mono::Type::Named(mono::NamedType { name, args }) => {
                    let ty_decl: &mono::TypeDecl =
                        mono_pgm.ty.get(name).unwrap().get(args).unwrap();

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
                                let mut field_idx: u32 = 0;
                                for (field_idx_, ty_field_name) in named_fields.keys().enumerate() {
                                    if ty_field_name == field {
                                        field_idx = field_idx_ as u32;
                                        break;
                                    }
                                }
                                field_idx
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
                    let mut field_idx: u32 = 0;
                    for (field_idx_, record_field_name) in fields.keys().enumerate() {
                        if record_field_name == field {
                            field_idx = field_idx_ as u32;
                            break;
                        }
                    }
                    field_idx
                }

                mono::Type::Variant { .. } => {
                    panic!("BUG: {}: FieldSel of variant", loc_display(loc))
                }

                mono::Type::Fn(_) => panic!("BUG: {}: FieldSel of function", loc_display(loc)),
            };

            (
                Expr::FieldSel(FieldSelExpr {
                    object,
                    field: field.clone(),
                    idx: field_idx,
                    object_ty,
                }),
                Default::default(),
            )
        }

        mono::Expr::AssocFnSel(mono::AssocFnSelExpr {
            ty_id,
            member,
            ty_args,
            ty: _,
        }) => {
            let fun_idx = *indices
                .assoc_funs
                .get(ty_id)
                .unwrap()
                .get(member)
                .unwrap()
                .get(ty_args)
                .unwrap();

            (Expr::Fun(fun_idx), Default::default())
        }

        mono::Expr::Call(mono::CallExpr { fun, args, ty: _ }) => {
            let fun_ty = fun.node.ty();

            let (fun, _fun_vars) = lower_bl_expr(fun, closures, indices, scope, mono_pgm);

            let mono::FnType {
                args: arg_tys,
                ret,
                exn,
            } = match fun_ty {
                mono::Type::Fn(fun_ty) => fun_ty,

                mono::Type::Named(_) | mono::Type::Record { .. } | mono::Type::Variant { .. } => {
                    panic!(
                        "BUG: {}: Function in call expression does not have a function type: {}",
                        loc_display(loc),
                        fun_ty,
                    )
                }
            };

            let expr: Expr = match arg_tys {
                mono::FunArgs::Positional(arg_tys) => {
                    let args = args
                        .iter()
                        .map(|mono::CallArg { name: _, expr }| {
                            lower_l_expr(expr, closures, indices, scope, mono_pgm).0
                        })
                        .collect();

                    match &fun.node {
                        Expr::Con(heap_obj_idx) => Expr::ConAlloc {
                            con_idx: *heap_obj_idx,
                            args,
                            arg_tys: arg_tys.clone(),
                            ret_ty: (*ret).clone(),
                        },
                        _ => Expr::Call(CallExpr {
                            fun,
                            args,
                            fun_ty: mono::FnType {
                                args: mono::FunArgs::Positional(arg_tys.clone()),
                                ret: ret.clone(),
                                exn: exn.clone(),
                            },
                        }),
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
                        Expr::Con(heap_obj_idx) => Expr::ConAlloc {
                            con_idx: *heap_obj_idx,
                            args,
                            arg_tys: named_args.values().cloned().collect(),
                            ret_ty: (*ret).clone(),
                        },
                        _ => Expr::Call(CallExpr {
                            fun,
                            args,
                            fun_ty: mono::FnType {
                                args: mono::FunArgs::Named(named_args.clone()),
                                ret: ret.clone(),
                                exn: exn.clone(),
                            },
                        }),
                    };

                    stmts.push(L {
                        node: Stmt::Expr(call_expr),
                        loc: loc.clone(),
                    });

                    Expr::Do(stmts, (*ret).clone())
                }
            };

            (expr, Default::default())
        }

        mono::Expr::Int(int) => {
            let kind = int.kind.unwrap();
            let value = match kind {
                ast::IntKind::I8(val) => val as u8 as u64,
                ast::IntKind::U8(val) => val as u64,
                ast::IntKind::I32(val) => val as u32 as u64,
                ast::IntKind::U32(val) => val as u64,
                ast::IntKind::I64(val) => val as u64,
                ast::IntKind::U64(val) => val,
            };
            (Expr::Int(value), Default::default())
        }

        mono::Expr::Str(str) => (Expr::Str(str.clone()), Default::default()),

        mono::Expr::Char(char) => (
            Expr::ConAlloc {
                con_idx: *indices
                    .product_cons
                    .get(&SmolStr::new_static("Char"))
                    .unwrap()
                    .get(&vec![])
                    .unwrap(),
                args: vec![L {
                    loc: loc.clone(),
                    node: Expr::Int(u64::from(*char as u32)),
                }],
                arg_tys: vec![mono::Type::u32()],
                ret_ty: mono::Type::char(),
            },
            Default::default(),
        ),

        mono::Expr::BoolOr(left, right) => {
            let (left, left_vars) = lower_bl_expr(left, closures, indices, scope, mono_pgm);
            scope.bounds.push_scope(left_vars);
            let (right, right_vars) = lower_bl_expr(right, closures, indices, scope, mono_pgm);
            let mut left_vars = scope.bounds.exit();
            left_vars.extend(right_vars);
            (Expr::BoolOr(left, right), left_vars)
        }

        mono::Expr::BoolAnd(left, right) => {
            let (left, left_vars) = lower_bl_expr(left, closures, indices, scope, mono_pgm);
            scope.bounds.push_scope(left_vars);
            let (right, right_vars) = lower_bl_expr(right, closures, indices, scope, mono_pgm);
            let mut left_vars = scope.bounds.exit();
            left_vars.extend(right_vars);
            (Expr::BoolAnd(left, right), left_vars)
        }

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

            let ty = mono::Type::Record {
                fields: field_tys.clone(),
            };

            stmts.push(L {
                node: Stmt::Expr(Expr::ConAlloc {
                    con_idx: record_idx,
                    args: field_tys
                        .keys()
                        .map(|name| L {
                            node: Expr::LocalVar(*arg_locals.get(name).unwrap()),
                            loc: loc.clone(),
                        })
                        .collect(),
                    arg_tys: field_tys.values().cloned().collect(),
                    ret_ty: ty.clone(),
                }),
                loc: loc.clone(),
            });

            (Expr::Do(stmts, ty), Default::default())
        }

        mono::Expr::Return(expr, ty) => {
            let (expr, _pat_vars) = lower_bl_expr(expr, closures, indices, scope, mono_pgm);
            (Expr::Return(expr, ty.clone()), Default::default())
        }

        mono::Expr::Match(mono::MatchExpr {
            scrutinee,
            alts,
            ty,
        }) => {
            let scrut_ty = scrutinee.node.ty();

            let (scrutinee, scrut_vars) =
                lower_bl_expr(scrutinee, closures, indices, scope, mono_pgm);
            scope.bounds.push_scope(scrut_vars);

            let alts = alts
                .iter()
                .map(|mono::Alt { pat, guard, rhs }| {
                    scope.bounds.enter();
                    let pat = lower_l_pat(pat, indices, scope, mono_pgm, &mut Default::default());
                    let guard = guard
                        .as_ref()
                        .map(|guard| lower_l_expr(guard, closures, indices, scope, mono_pgm));
                    if let Some((_guard, guard_vars)) = guard.as_ref() {
                        scope.bounds.push_scope(guard_vars.clone());
                    }
                    let rhs = rhs
                        .iter()
                        .map(|stmt| lower_l_stmt(stmt, closures, indices, scope, mono_pgm))
                        .collect();
                    if guard.is_some() {
                        scope.bounds.exit(); // pop guard's variables
                    }
                    scope.bounds.exit(); // pop pattern's variables
                    Alt {
                        pat,
                        guard: guard.map(|(guard, _guard_vars)| guard),
                        rhs,
                    }
                })
                .collect();

            scope.bounds.exit(); // pop scrutinee's variables

            (
                Expr::Match(MatchExpr {
                    scrutinee,
                    alts,
                    scrut_ty,
                    ty: ty.clone(),
                }),
                Default::default(),
            )
        }

        mono::Expr::If(mono::IfExpr {
            branches,
            else_branch,
            ty,
        }) => (
            Expr::If(IfExpr {
                branches: branches
                    .iter()
                    .map(|(cond, rhs)| {
                        let (cond, pat_vars) =
                            lower_l_expr(cond, closures, indices, scope, mono_pgm);
                        scope.bounds.push_scope(pat_vars);
                        let rhs = rhs
                            .iter()
                            .map(|stmt| lower_l_stmt(stmt, closures, indices, scope, mono_pgm))
                            .collect();
                        scope.bounds.exit();
                        (cond, rhs)
                    })
                    .collect(),
                else_branch: else_branch.as_ref().map(|stmts| {
                    stmts
                        .iter()
                        .map(|stmt| lower_l_stmt(stmt, closures, indices, scope, mono_pgm))
                        .collect()
                }),
                ty: ty.clone(),
            }),
            Default::default(),
        ),

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
                .map(|stmt| lower_l_stmt(stmt, closures, indices, &mut closure_scope, mono_pgm))
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

            (Expr::ClosureAlloc(closure_idx), Default::default())
        }

        mono::Expr::Is(mono::IsExpr { expr, pat }) => {
            let expr_ty = expr.node.ty();
            scope.bounds.enter();
            let (expr, _pat_vars_1) = lower_bl_expr(expr, closures, indices, scope, mono_pgm);
            let pat = lower_l_pat(pat, indices, scope, mono_pgm, &mut Default::default());
            let pat_vars_2 = scope.bounds.exit();
            (Expr::Is(IsExpr { expr, pat, expr_ty }), pat_vars_2)
        }

        mono::Expr::Do(stmts, ty) => {
            scope.bounds.enter();
            let expr = Expr::Do(
                stmts
                    .iter()
                    .map(|stmt| lower_l_stmt(stmt, closures, indices, scope, mono_pgm))
                    .collect(),
                ty.clone(),
            );
            scope.bounds.exit();
            (expr, Default::default())
        }

        mono::Expr::Variant(mono::VariantExpr { expr, ty }) => {
            // Note: Type of the expr in the variant won't be a variant type. Use the
            // `VariantExpr`'s type.
            let expr_ty = expr.node.ty();
            let (expr, vars) = lower_bl_expr(expr, closures, indices, scope, mono_pgm);
            (
                Expr::Variant {
                    expr,
                    expr_ty,
                    variant_ty: ty.clone(),
                },
                vars,
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
) -> (L<Expr>, HashMap<Id, LocalIdx>) {
    let (expr, pat_vars) = lower_expr(
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
    )
}

fn lower_bl_expr(
    bl_expr: &L<mono::Expr>,
    closures: &mut Vec<Closure>,
    indices: &Indices,
    scope: &mut FunScope,
    mono_pgm: &mono::MonoPgm,
) -> (Box<L<Expr>>, HashMap<Id, LocalIdx>) {
    let (expr, pat_vars) = lower_l_expr(bl_expr, closures, indices, scope, mono_pgm);
    (Box::new(expr), pat_vars)
}

fn lower_pat(
    pat: &mono::Pat,
    indices: &Indices,
    scope: &mut FunScope,
    mono_pgm: &mono::MonoPgm,
    loc: &Loc,

    // This map is to map binders in alternatives of or patterns to the same local.
    //
    // Only in or-pattern alternatives we allow same binders, so if we see a binder for the second
    // time, we must be checking another alternative of an or-pattern.
    mapped_binders: &mut HashMap<Id, LocalIdx>,
) -> Pat {
    match pat {
        mono::Pat::Var(mono::VarPat { var, ty, refined }) => match mapped_binders.get(var) {
            Some(idx) => Pat::Var(VarPat {
                idx: *idx,
                original_ty: ty.clone(),
            }),
            None => {
                let var_idx = LocalIdx(scope.locals.len() as u32);
                scope.locals.push(LocalInfo {
                    name: var.clone(),
                    ty: refined.as_ref().unwrap_or(ty).clone(),
                });
                scope.bounds.insert(var.clone(), var_idx);
                mapped_binders.insert(var.clone(), var_idx);
                Pat::Var(VarPat {
                    idx: var_idx,
                    original_ty: ty.clone(),
                })
            }
        },

        mono::Pat::Con(mono::ConPat {
            con:
                mono::Con {
                    ty_id: ty,
                    con,
                    ty_args,
                    ty: _,
                },
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

        mono::Pat::Variant(mono::VariantPat {
            pat,
            variant_ty,
            pat_ty,
        }) => Pat::Variant {
            pat: Box::new(lower_l_pat(pat, indices, scope, mono_pgm, mapped_binders)),
            variant_ty: variant_ty.clone(),
            pat_ty: pat_ty.clone(),
        },
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
    sig: &mono::FunSig,
    body: &[L<mono::Stmt>],
    indices: &Indices,
    closures: &mut Vec<Closure>,
    mono_pgm: &mono::MonoPgm,
) -> SourceFunDecl {
    let mut locals: Vec<LocalInfo> = vec![];
    let mut bounds: ScopeMap<Id, LocalIdx> = Default::default();

    for (param, ty) in &sig.params {
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

    let body: Vec<L<Stmt>> = body
        .iter()
        .map(|stmt| lower_l_stmt(stmt, closures, indices, &mut scope, mono_pgm))
        .collect();

    SourceFunDecl {
        body,
        locals: scope.locals,
    }
}
