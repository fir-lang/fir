//! Numbering pass lowers monomorphic AST to eliminate type arguments. All function and consturctor
//! references are converted into indices by this pass.

pub mod printer;

use crate::collections::*;
use crate::mono_ast::{self as mono, AssignOp, Id, IntExpr, Named, UnOp, L};
use crate::record_collector::{collect_records, RecordShape, VariantShape};

use smol_str::SmolStr;

#[derive(Debug)]
pub struct LoweredPgm {
    pub heap_objs: Vec<HeapObj>,
    pub funs: Vec<Fun>,
    pub closures: Vec<Closure>,

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
    pub array_u8_con_idx: HeapObjIdx,
    pub array_u32_con_idx: HeapObjIdx,
    pub array_u64_con_idx: HeapObjIdx,
    pub result_err_cons: Map<Vec<mono::Type>, HeapObjIdx>,
    pub result_ok_cons: Map<Vec<mono::Type>, HeapObjIdx>,
}

pub const CONSTR_CON_IDX: HeapObjIdx = HeapObjIdx(0);
pub const FUN_CON_IDX: HeapObjIdx = HeapObjIdx(1);
pub const METHOD_CON_IDX: HeapObjIdx = HeapObjIdx(2);
pub const CLOSURE_CON_IDX: HeapObjIdx = HeapObjIdx(3);
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
                    "Char" => Repr::U32,
                    "Bool" => Repr::U8,
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
    U8AsI8,
    U8AsU32,
    U32AsU8,
    U32AsI32,
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
    ///
    /// This function never throws or returns, so we don't need the exception and return types.
    Throw,

    /// `prim try(cb: Fn(): {..exn} a): {..r} Result[[..exn], a]`
    ///
    /// We don't store the `r` type parameter as this function never throws.
    Try {
        /// Type of exceptions to catch.
        exn: mono::Type,

        /// The return type of the callback.
        a: mono::Type,
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
    pub name: L<Id>,              // for debugging and to find the main function in the interpreter
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

/// Describes heap allocated objects.
#[derive(Debug)]
pub enum HeapObj {
    Builtin(BuiltinConDecl),
    Source(SourceConDecl),
    Record(RecordShape),
    Variant(VariantShape),
}

impl HeapObj {
    pub fn as_source_con(&self) -> &SourceConDecl {
        match self {
            HeapObj::Source(con) => con,
            _ => panic!(),
        }
    }

    pub fn as_record(&self) -> &RecordShape {
        match self {
            HeapObj::Record(record) => record,
            _ => panic!(),
        }
    }

    pub fn as_variant(&self) -> &VariantShape {
        match self {
            HeapObj::Variant(variant) => variant,
            _ => panic!(),
        }
    }
}

#[derive(Debug)]
pub enum BuiltinConDecl {
    /// Constructor closure, e.g. `Option.Some`, `Char`.
    ///
    /// Payload holds the constructor index (`ConIdx`).
    Constr,

    /// Function closure, e.g. `id`, `Vec.withCapacity`.
    ///
    /// Payload holds the function index (`FunIdx`).
    Fun,

    /// Method closure, e.g. `x.toString`.
    ///
    /// Payload holds the receiver and function index (`FunIdx`), in that order.
    Method,

    /// A function expression.
    ///
    /// Payload holds the closure index (`ClosureIdx`), then free variables.
    Closure,

    ArrayU8,
    ArrayU32,
    ArrayU64,
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
    pub idx: HeapObjIdx,          // for debugging
    pub ty_args: Vec<mono::Type>, // for debugging
    pub fields: ConFields,

    /// For interpeter: if the constructor doesn't have any fields, this holds the address to the
    /// singleton allocation.
    pub alloc: u64,
}

#[derive(Debug)]
pub enum ConFields {
    Named(Vec<(Id, Ty)>),
    Unnamed(Vec<Ty>),
}

impl ConFields {
    pub fn is_empty(&self) -> bool {
        match self {
            ConFields::Named(fields) => fields.is_empty(),
            ConFields::Unnamed(fields) => fields.is_empty(),
        }
    }

    pub fn find_named_field_idx(&self, id: &Id) -> usize {
        match self {
            ConFields::Unnamed(_) => panic!(),
            ConFields::Named(fields) => fields
                .iter()
                .enumerate()
                .find_map(|(i, field)| if &field.0 == id { Some(i) } else { None })
                .unwrap(),
        }
    }
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
    pub pat: L<Pat>,
    pub expr: L<Expr>,
    pub body: Vec<L<Stmt>>,

    /// The `next` method to call on the iterator.
    pub next_method: FunIdx,

    /// Heap object for the `Option.Some` constructor that iterator returns.
    pub option_some_con: HeapObjIdx,
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
    Constr(HeapObjIdx),             // a product constructor
    FieldSelect(FieldSelectExpr),   // <expr>.<id> (TODO: This could be lowered as function calls)
    MethodSelect(MethodSelectExpr), // <id>.<id>, with an object captured as receiver
    AssocFnSelect(FunIdx),          // <id>.<id>
    Call(CallExpr),
    Int(IntExpr),
    String(Vec<StringPart>),
    Char(char),
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
pub struct RecordExpr {
    pub fields: Vec<Named<L<Expr>>>,
    pub idx: HeapObjIdx,
}

#[derive(Debug, Clone)]
pub struct VariantExpr {
    pub id: Id,
    pub fields: Vec<Named<L<Expr>>>,
    pub idx: HeapObjIdx,
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
    pub constr: HeapObjIdx,
    pub fields: Vec<Named<L<Pat>>>,
}

#[derive(Debug, Clone)]
pub struct RecordPattern {
    pub fields: Vec<Named<L<Pat>>>,
    pub idx: HeapObjIdx,
}

#[derive(Debug, Clone)]
pub struct VariantPattern {
    pub constr: Id,
    pub fields: Vec<Named<L<Pat>>>,
    pub idx: HeapObjIdx,
}

#[derive(Debug)]
pub struct Closure {
    pub idx: ClosureIdx, // for debugging
    pub locals: Vec<LocalInfo>,
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
    pub use_idx: LocalIdx,
}

////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
struct Indices {
    product_cons: Map<Id, Map<Vec<mono::Type>, HeapObjIdx>>,
    sum_cons: Map<Id, Map<Id, Map<Vec<mono::Type>, HeapObjIdx>>>,
    funs: Map<Id, Map<Vec<mono::Type>, FunIdx>>,
    assoc_funs: Map<Id, Map<Id, Map<Vec<mono::Type>, FunIdx>>>,
    records: Map<RecordShape, HeapObjIdx>,
    variants: Map<VariantShape, HeapObjIdx>,
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
    captured_vars: Map<Id, ClosureFv>,

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
    fn use_var(&mut self, var: &Id) -> LocalIdx {
        // Check if bound.
        match self.bounds.get(var) {
            Some(idx) => *idx,
            None => {
                // Should be bound in parent function. Reuse the index if we already assigned it
                // one.
                match self.captured_vars.get(var) {
                    Some(fv) => fv.use_idx,
                    None => {
                        // Use the variable in the parent function so that the parent function will
                        // capture it if it needs to.
                        let alloc_idx = self.parent_fun_scope.as_mut().unwrap().use_var(var);
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
    }
}

pub fn lower(mono_pgm: &mut mono::MonoPgm) -> LoweredPgm {
    // Number all declarations first, then lower the program.
    let mut product_con_nums: Map<Id, Map<Vec<mono::Type>, HeapObjIdx>> = Default::default();
    let mut sum_con_nums: Map<Id, Map<Id, Map<Vec<mono::Type>, HeapObjIdx>>> = Default::default();
    let mut fun_nums: Map<Id, Map<Vec<mono::Type>, FunIdx>> = Default::default();
    let mut assoc_fun_nums: Map<Id, Map<Id, Map<Vec<mono::Type>, FunIdx>>> = Default::default();

    // Number type declarations.
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
                    // No RHS means it's either an uninhabited type like Void or a primitive. We
                    // can't distinguish the two here, so we assume primitive and give a number to
                    // all types without a RHS.
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
        array_u8_con_idx: *product_con_nums
            .get("Array")
            .unwrap()
            .get(&vec![mono::Type::Named(mono::NamedType {
                name: SmolStr::new("U8"),
                args: vec![],
            })])
            .unwrap(),
        array_u32_con_idx: *product_con_nums
            .get("Array")
            .unwrap()
            .get(&vec![mono::Type::Named(mono::NamedType {
                name: SmolStr::new("U32"),
                args: vec![],
            })])
            .unwrap(),
        array_u64_con_idx: *product_con_nums
            .get("Array")
            .unwrap()
            .get(&vec![mono::Type::Named(mono::NamedType {
                name: SmolStr::new("U64"),
                args: vec![],
            })])
            .unwrap(),
        result_err_cons: sum_con_nums
            .get_mut(&SmolStr::new_static("Result"))
            .and_then(|r| r.get(&SmolStr::new_static("Err")).cloned())
            .unwrap_or_default(),
        result_ok_cons: sum_con_nums
            .get_mut(&SmolStr::new_static("Result"))
            .and_then(|r| r.get(&SmolStr::new_static("Ok")).cloned())
            .unwrap_or_default(),
    };

    // Lower the program. Note that the iteration order here should be the same as above to add
    // right definitions to the right indices in the vectors.

    // Lower types. Add special built-ins first.
    lowered_pgm
        .heap_objs
        .push(HeapObj::Builtin(BuiltinConDecl::Constr));
    lowered_pgm
        .heap_objs
        .push(HeapObj::Builtin(BuiltinConDecl::Fun));
    lowered_pgm
        .heap_objs
        .push(HeapObj::Builtin(BuiltinConDecl::Method));
    lowered_pgm
        .heap_objs
        .push(HeapObj::Builtin(BuiltinConDecl::Closure));

    for (con_id, con_ty_map) in &mono_pgm.ty {
        for (con_ty_args, con_decl) in con_ty_map {
            match &con_decl.rhs {
                Some(rhs) => match rhs {
                    mono::TypeDeclRhs::Sum(cons) => {
                        for mono::ConstructorDecl { name, fields } in cons {
                            let idx = HeapObjIdx(lowered_pgm.heap_objs.len() as u32);
                            let name = SmolStr::new(format!("{}.{}", con_id, name));
                            lowered_pgm.heap_objs.push(lower_source_con(
                                idx,
                                &name,
                                con_ty_args,
                                fields,
                            ));
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
                        lowered_pgm.heap_objs.push(HeapObj::Builtin(array_con));
                    }

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

                    "Void" => {
                        assert_eq!(con_ty_args.len(), 0);
                        // Lower as unit as we can't express empty types in the lowered
                        // representation.
                        // TODO: Could we just skip this?
                        // NOTE: This needs to be in sync with the numbering loop above.
                        let idx = HeapObjIdx(lowered_pgm.heap_objs.len() as u32);
                        lowered_pgm.heap_objs.push(HeapObj::Source(SourceConDecl {
                            name: SmolStr::new_static("Void"),
                            idx,
                            ty_args: vec![],
                            fields: ConFields::Unnamed(vec![]),
                            alloc: u64::MAX, // a value that causes errors if accidentally used
                        }))
                    }

                    other => panic!("Unknown built-in type: {}", other),
                },
            }
        }
    }

    // Assign indices to record and variant shapes.
    let (record_shapes, variant_shapes) = collect_records(mono_pgm);

    let mut record_indices: Map<RecordShape, HeapObjIdx> = Default::default();
    for record_shape in record_shapes {
        let idx = next_con_idx;
        next_con_idx = HeapObjIdx(next_con_idx.0 + 1);
        record_indices.insert(record_shape.clone(), idx);
        lowered_pgm.heap_objs.push(HeapObj::Record(record_shape));
    }

    let mut variant_indices: Map<VariantShape, HeapObjIdx> = Default::default();
    for variant_shape in variant_shapes {
        let idx = next_con_idx;
        next_con_idx = HeapObjIdx(next_con_idx.0 + 1);
        variant_indices.insert(variant_shape.clone(), idx);
        lowered_pgm.heap_objs.push(HeapObj::Variant(variant_shape));
    }

    let mut indices = Indices {
        product_cons: product_con_nums,
        sum_cons: sum_con_nums,
        funs: fun_nums,
        assoc_funs: assoc_fun_nums,
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
                        lowered_pgm
                            .funs
                            .push(Fun::Builtin(BuiltinFunDecl::Try { exn, a }));
                    }

                    "throw" => {
                        // prim throw(exn: [..r]): {..r} a
                        assert_eq!(fun_ty_args.len(), 2); // r, a
                        lowered_pgm.funs.push(Fun::Builtin(BuiltinFunDecl::Throw));
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

                        ("U32", "asI32") => {
                            assert_eq!(fun_ty_args.len(), 1); // exception
                            lowered_pgm
                                .funs
                                .push(Fun::Builtin(BuiltinFunDecl::U32AsI32));
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
    idx: HeapObjIdx,
    con_id: &SmolStr,
    con_ty_args: &[mono::Type],
    fields: &mono::ConstructorFields,
) -> HeapObj {
    HeapObj::Source(SourceConDecl {
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
        alloc: u64::MAX, // a value that causes errors if accidentally used
    })
}

fn lower_stmt(
    stmt: &mono::Stmt,
    closures: &mut Vec<Closure>,
    indices: &mut Indices,
    scope: &mut FunScope,
) -> Stmt {
    match stmt {
        mono::Stmt::Let(mono::LetStmt { lhs, rhs }) => Stmt::Let(LetStmt {
            lhs: lower_l_pat(lhs, indices, scope),
            rhs: lower_l_expr(rhs, closures, indices, scope),
        }),

        mono::Stmt::Assign(mono::AssignStmt { lhs, rhs, op }) => Stmt::Assign(AssignStmt {
            lhs: lower_l_expr(lhs, closures, indices, scope),
            rhs: lower_l_expr(rhs, closures, indices, scope),
            op: *op,
        }),

        mono::Stmt::Expr(expr) => Stmt::Expr(lower_l_expr(expr, closures, indices, scope)),

        mono::Stmt::For(mono::ForStmt {
            pat,
            expr,
            body,
            iter_ty,
            item_ty,
        }) => {
            let next_method = *indices
                .assoc_funs
                .get("Iterator")
                .unwrap()
                .get("next")
                .unwrap()
                .get(&vec![
                    iter_ty.clone(),
                    item_ty.clone(),
                    // exception type passed as empty variant by monomorphiser
                    // TODO: Maybe store exception type in the statement.
                    mono::Type::Variant { alts: vec![] },
                ])
                .unwrap();

            let option_some_con = *indices
                .sum_cons
                .get("Option")
                .unwrap()
                .get("Some")
                .unwrap()
                .get(&vec![item_ty.clone()])
                .unwrap();

            let expr = lower_l_expr(expr, closures, indices, scope);
            scope.bounds.enter();
            let pat = lower_l_pat(pat, indices, scope);
            let body = body
                .iter()
                .map(|stmt| lower_l_stmt(stmt, closures, indices, scope))
                .collect();
            scope.bounds.exit();

            Stmt::For(ForStmt {
                pat,
                expr,
                body,
                next_method,
                option_some_con,
            })
        }

        mono::Stmt::While(mono::WhileStmt { label, cond, body }) => Stmt::While(WhileStmt {
            label: label.clone(),
            cond: lower_l_expr(cond, closures, indices, scope),
            body: body
                .iter()
                .map(|stmt| lower_l_stmt(stmt, closures, indices, scope))
                .collect(),
        }),

        mono::Stmt::WhileLet(mono::WhileLetStmt {
            label,
            pat,
            cond,
            body,
        }) => {
            let cond = lower_l_expr(cond, closures, indices, scope);
            scope.bounds.enter();
            let pat = lower_l_pat(pat, indices, scope);
            let body = body
                .iter()
                .map(|stmt| lower_l_stmt(stmt, closures, indices, scope))
                .collect();
            scope.bounds.exit();
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
    indices: &mut Indices,
    scope: &mut FunScope,
) -> L<Stmt> {
    stmt.map_as_ref(|stmt| lower_stmt(stmt, closures, indices, scope))
}

fn lower_expr(
    expr: &mono::Expr,
    _loc: &mono::Loc,
    closures: &mut Vec<Closure>,
    indices: &mut Indices,
    scope: &mut FunScope,
) -> Expr {
    match expr {
        mono::Expr::LocalVar(var) => Expr::LocalVar(scope.use_var(var)),

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
                object: lower_bl_expr(object, closures, indices, scope),
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
                object: lower_bl_expr(object, closures, indices, scope),
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
            fun: lower_bl_expr(fun, closures, indices, scope),
            args: args
                .iter()
                .map(|mono::CallArg { name, expr }| CallArg {
                    name: name.clone(),
                    expr: lower_l_expr(expr, closures, indices, scope),
                })
                .collect(),
        }),

        mono::Expr::Int(int) => Expr::Int(int.clone()),

        mono::Expr::String(parts) => Expr::String(
            parts
                .iter()
                .map(|part| match part {
                    mono::StringPart::Str(str) => StringPart::Str(str.clone()),
                    mono::StringPart::Expr(expr) => {
                        StringPart::Expr(lower_l_expr(expr, closures, indices, scope))
                    }
                })
                .collect(),
        ),

        mono::Expr::Char(char) => Expr::Char(*char),

        mono::Expr::Self_ => Expr::LocalVar(LocalIdx(0)),

        mono::Expr::BinOp(mono::BinOpExpr {
            left,
            right,
            op: mono::BinOp::And,
        }) => Expr::BoolAnd(
            lower_bl_expr(left, closures, indices, scope),
            lower_bl_expr(right, closures, indices, scope),
        ),

        mono::Expr::BinOp(mono::BinOpExpr {
            left,
            right,
            op: mono::BinOp::Or,
        }) => Expr::BoolOr(
            lower_bl_expr(left, closures, indices, scope),
            lower_bl_expr(right, closures, indices, scope),
        ),

        mono::Expr::BinOp(_) => panic!("Non-desugared BinOp"),

        mono::Expr::UnOp(mono::UnOpExpr { op, expr }) => match op {
            UnOp::Neg => panic!("Neg unop wasn't desugred"),
            UnOp::Not => Expr::BoolNot(lower_bl_expr(expr, closures, indices, scope)),
        },

        mono::Expr::Record(fields) => {
            let idx = *indices
                .records
                .get(&RecordShape::from_named_things(fields))
                .unwrap();
            Expr::Record(RecordExpr {
                fields: fields
                    .iter()
                    .map(|field| lower_nl_expr(field, closures, indices, scope))
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
                    .map(|arg| lower_nl_expr(arg, closures, indices, scope))
                    .collect(),
                idx,
            })
        }

        mono::Expr::Return(expr) => Expr::Return(lower_bl_expr(expr, closures, indices, scope)),

        mono::Expr::Match(mono::MatchExpr { scrutinee, alts }) => Expr::Match(MatchExpr {
            scrutinee: lower_bl_expr(scrutinee, closures, indices, scope),
            alts: alts
                .iter()
                .map(
                    |mono::Alt {
                         pattern,
                         guard,
                         rhs,
                     }| {
                        scope.bounds.enter();
                        let pattern = lower_l_pat(pattern, indices, scope);
                        let guard = guard
                            .as_ref()
                            .map(|guard| lower_l_expr(guard, closures, indices, scope));
                        let rhs = rhs
                            .iter()
                            .map(|stmt| lower_l_stmt(stmt, closures, indices, scope))
                            .collect();
                        scope.bounds.exit();
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
                        lower_l_expr(cond, closures, indices, scope),
                        rhs.iter()
                            .map(|stmt| lower_l_stmt(stmt, closures, indices, scope))
                            .collect(),
                    )
                })
                .collect(),
            else_branch: else_branch.as_ref().map(|stmts| {
                stmts
                    .iter()
                    .map(|stmt| lower_l_stmt(stmt, closures, indices, scope))
                    .collect()
            }),
        }),

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
                .map(|stmt| lower_l_stmt(stmt, closures, indices, &mut closure_scope))
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
                params: sig
                    .params
                    .iter()
                    .map(|(_, ty)| Ty::from_mono_ty(&ty.node))
                    .collect(),
                body,
            });

            Expr::ClosureAlloc(closure_idx)
        }
    }
}

fn lower_nl_expr(
    expr: &Named<L<mono::Expr>>,
    closures: &mut Vec<Closure>,
    indices: &mut Indices,
    scope: &mut FunScope,
) -> Named<L<Expr>> {
    expr.map_as_ref(|expr| lower_l_expr(expr, closures, indices, scope))
}

fn lower_l_expr(
    l_expr: &L<mono::Expr>,
    closures: &mut Vec<Closure>,
    indices: &mut Indices,
    scope: &mut FunScope,
) -> L<Expr> {
    l_expr.map_as_ref(|expr| lower_expr(expr, &l_expr.loc, closures, indices, scope))
}

fn lower_bl_expr(
    bl_expr: &L<mono::Expr>,
    closures: &mut Vec<Closure>,
    indices: &mut Indices,
    scope: &mut FunScope,
) -> Box<L<Expr>> {
    Box::new(bl_expr.map_as_ref(|expr| lower_expr(expr, &bl_expr.loc, closures, indices, scope)))
}

fn lower_pat(pat: &mono::Pat, indices: &mut Indices, scope: &mut FunScope) -> Pat {
    match pat {
        mono::Pat::Var(mono::VarPat { var, ty }) => {
            let var_idx = LocalIdx(scope.locals.len() as u32);
            scope.locals.push(LocalInfo {
                name: var.clone(),
                ty: ty.clone(),
            });
            scope.bounds.insert(var.clone(), var_idx);
            Pat::Var(var_idx)
        }

        mono::Pat::Constr(mono::ConstrPattern {
            constr: mono::Constructor { type_, constr },
            fields,
            ty_args,
        }) => {
            let con_idx: HeapObjIdx = match constr {
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
                    .map(|named_f| named_f.map_as_ref(|f| lower_l_pat(f, indices, scope)))
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
                    .map(|field| lower_nl_pat(field, indices, scope))
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
                    .map(|field| lower_nl_pat(field, indices, scope))
                    .collect(),
                idx,
            })
        }

        mono::Pat::Ignore => Pat::Ignore,

        mono::Pat::Str(str) => Pat::Str(str.clone()),

        mono::Pat::Char(char) => Pat::Char(*char),

        mono::Pat::StrPfx(str, var) => {
            let var_idx = LocalIdx(scope.locals.len() as u32);
            scope.locals.push(LocalInfo {
                name: var.clone(),
                ty: mono::Type::Named(mono::NamedType {
                    name: "Str".into(),
                    args: vec![],
                }),
            });
            scope.bounds.insert(var.clone(), var_idx);
            Pat::StrPfx(str.clone(), var_idx)
        }

        mono::Pat::Or(p1, p2) => Pat::Or(
            Box::new(lower_l_pat(p1, indices, scope)),
            Box::new(lower_l_pat(p2, indices, scope)),
        ),
    }
}

fn lower_nl_pat(
    pat: &Named<L<mono::Pat>>,
    indices: &mut Indices,
    scope: &mut FunScope,
) -> Named<L<Pat>> {
    pat.map_as_ref(|pat| lower_l_pat(pat, indices, scope))
}

fn lower_l_pat(pat: &L<mono::Pat>, indices: &mut Indices, scope: &mut FunScope) -> L<Pat> {
    pat.map_as_ref(|pat| lower_pat(pat, indices, scope))
}

fn lower_source_fun(
    fun: &mono::FunDecl,
    idx: FunIdx,
    ty_args: &[mono::Type],
    indices: &mut Indices,
    closures: &mut Vec<Closure>,
) -> SourceFunDecl {
    let mut locals: Vec<LocalInfo> = vec![];
    let mut bounds: ScopeMap<Id, LocalIdx> = Default::default();
    let mut params: Vec<Ty> = vec![];

    match &fun.sig.self_ {
        mono::SelfParam::No => {}

        mono::SelfParam::Implicit => {
            // Same as the type checker: function should be an associated function, and the parent
            // type should not have type parameters.
            // TODO: Type checker should annotate all self types instead.
            let self_ty_con = fun.parent_ty.as_ref().unwrap().node.clone();
            let self_mono_ty = mono::Type::Named(mono::NamedType {
                name: self_ty_con,
                args: vec![],
            });
            params.push(Ty::from_mono_ty(&self_mono_ty));
            locals.push(LocalInfo {
                name: SmolStr::new_static("self"),
                ty: self_mono_ty,
            });
        }
        mono::SelfParam::Explicit(self_ty) => {
            params.push(Ty::from_mono_ty(&self_ty.node));
            locals.push(LocalInfo {
                name: SmolStr::new_static("self"),
                ty: self_ty.node.clone(),
            });
            bounds.insert(SmolStr::new_static("self"), LocalIdx(0));
        }
    }

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
        .map(|stmt| lower_l_stmt(stmt, closures, indices, &mut scope))
        .collect();

    params.extend(
        fun.sig
            .params
            .iter()
            .map(|(_, param_ty)| Ty::from_mono_ty(&param_ty.node)),
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
