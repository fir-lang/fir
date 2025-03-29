#![allow(clippy::needless_range_loop, clippy::too_many_arguments)]

const INITIAL_HEAP_SIZE_WORDS: usize = (1024 * 1024 * 1024) / 8; // 1 GiB

// mod builtins;
mod heap;
// mod init;

// use builtins::{call_builtin_fun, BuiltinFun};
use heap::Heap;

use crate::ast::{self, Id, Loc, L};
use crate::collections::Map;
use crate::interpolation::StringPart;
use crate::lowering::*;
use crate::record_collector::{RecordShape, VariantShape};
use crate::utils::loc_display;

use std::cmp::Ordering;
use std::io::Write;

use bytemuck::cast_slice_mut;
use smol_str::SmolStr;

// Just lowered program with some extra cached stuff for easy access.
struct Pgm {
    cons: Vec<Con>,
    funs: Vec<Fun>,
    closures: Vec<Closure>,
    records: Vec<RecordShape>,
    variants: Vec<VariantShape>,

    // Some allocations and type tags for the built-ins.
    true_alloc: u64,
    false_alloc: u64,
    char_con_idx: ConIdx,
    str_con_idx: ConIdx,
    i8_con_idx: ConIdx,
    u8_con_idx: ConIdx,
    i32_con_idx: ConIdx,
    u32_con_idx: ConIdx,
    array_i8_con_idx: ConIdx,
    array_u8_con_idx: ConIdx,
    array_i32_con_idx: ConIdx,
    array_u32_con_idx: ConIdx,
    array_i64_con_idx: ConIdx,
    array_u64_con_idx: ConIdx,
}

impl Pgm {
    fn init(lowered_pgm: LoweredPgm, heap: &mut Heap) -> Pgm {
        let LoweredPgm {
            mut cons,
            funs,
            closures,
            records,
            variants,
            true_con_idx,
            false_con_idx,
            char_con_idx,
            str_con_idx,
            i8_con_idx,
            u8_con_idx,
            i32_con_idx,
            u32_con_idx,
            array_i8_con_idx,
            array_u8_con_idx,
            array_i32_con_idx,
            array_u32_con_idx,
            array_i64_con_idx,
            array_u64_con_idx,
        } = lowered_pgm;

        // Allocate singletons for constructors without fields.
        for con in cons.iter_mut() {
            let source_con = match con {
                Con::Builtin(_) => continue,
                Con::Source(source_con) => source_con,
            };

            if !source_con.fields.is_empty() {
                continue;
            }

            source_con.alloc = heap.allocate_tag(source_con.idx.as_u64());
        }

        let true_alloc = cons[true_con_idx.as_usize()].as_source_con().alloc;
        let false_alloc = cons[false_con_idx.as_usize()].as_source_con().alloc;

        Pgm {
            cons,
            funs,
            closures,
            records,
            variants,
            true_alloc,
            false_alloc,
            char_con_idx,
            str_con_idx,
            i8_con_idx,
            u8_con_idx,
            i32_con_idx,
            u32_con_idx,
            array_i8_con_idx,
            array_u8_con_idx,
            array_i32_con_idx,
            array_u32_con_idx,
            array_i64_con_idx,
            array_u64_con_idx,
        }
    }
}

pub fn run<W: Write>(w: &mut W, pgm: LoweredPgm, main: &str, args: &[String]) {
    let mut heap = Heap::new();
    let pgm = Pgm::init(pgm, &mut heap);

    let main_fun: &SourceFunDecl = pgm
        .funs
        .iter()
        .find_map(|fun| match fun {
            Fun::Source(fun @ SourceFunDecl { name, .. }) if name.node.as_str() == main => {
                Some(fun)
            }
            _ => None,
        })
        .unwrap_or_else(|| panic!("Main function `{}` is not defined", main));

    // `main` doesn't have a call site, called by the interpreter.
    let call_loc = Loc {
        module: "".into(),
        line_start: 0,
        col_start: 0,
        byte_offset_start: 0,
        line_end: 0,
        col_end: 0,
        byte_offset_end: 0,
    };

    let mut heap = Heap::new();

    // Check if main takes an input argument.
    let arg_vec: Vec<u64> = match main_fun.params.len() {
        0 => {
            if args.len() > 1 {
                println!("WARNING: `main` does not take command line arguments, but command line arguments are passed to the interpreter");
            }
            vec![]
        }
        1 => {
            let arg_vec = heap.allocate(2 + args.len());
            heap[arg_vec] = pgm.array_u64_con_idx.as_u64();
            heap[arg_vec + 1] = args.len() as u64;
            for (i, arg) in args.iter().enumerate() {
                let arg_val = heap.allocate_str(
                    pgm.str_con_idx.as_u64(),
                    pgm.array_u8_con_idx.as_u64(),
                    arg.as_bytes(),
                );
                heap[arg_vec + 2 + (i as u64)] = arg_val;
            }
            vec![arg_vec]
        }
        other => panic!(
            "`main` needs to take 0 or 1 argument, but it takes {} arguments",
            other
        ),
    };

    todo!()
    // call_fun(w, &pgm, &mut heap, main_fun, arg_vec, &call_loc);
}

macro_rules! generate_tags {
    ($($name:ident),* $(,)?) => {
        generate_tags!(@generate 0, $($name),*);
    };

    (@generate $index:expr, $name:ident $(, $rest:ident)*) => {
        const $name: u64 = $index;
        generate_tags!(@generate $index + 1, $($rest),*);
    };

    (@generate $index:expr,) => {};
}

// NB. If you update this make sure you update built-in `TyCon`s in `collect_types`.
#[rustfmt::skip]
generate_tags!(
    CONSTR_TYPE_TAG,    // Constructor closure, e.g. `Option.Some`.
    TOP_FUN_TYPE_TAG,   // Top-level function closure, e.g. `id`.
    ASSOC_FUN_TYPE_TAG, // Associated function closure, e.g. `Value.toString`.
    METHOD_TYPE_TAG,    // Method closure, e.g. `x.toString`.
    CLOSURE_TYPE_TAG,
    FIRST_TYPE_TAG,     // First available type tag for user types.
);

/*
#[derive(Debug)]
struct Con {
    info: ConInfo,

    fields: Fields,

    /// For constructors with no fields, this holds the canonical allocation.
    alloc: Option<u64>,
}

#[derive(Debug)]
enum ConInfo {
    Named {
        ty_name: Id,
        con_name: Option<Id>,
    },
    Record {
        #[allow(unused)]
        shape: RecordShape,
    },
    Variant {
        #[allow(unused)]
        shape: VariantShape,
    },
}

#[derive(Debug, Clone)]
struct TyCon {
    /// Constructors of the type. E.g. `Some` and `None` in `Option`.
    ///
    /// Sorted based on tags.
    value_constrs: Vec<ValCon>,

    /// Type tag of the first value constructor of this type.
    ///
    /// For product types, this is the only tag values of this type use.
    ///
    /// For sum types, this is the first tag the values use.
    type_tag: u64,
}

impl TyCon {
    /// First and last tag (inclusive) that values of this type use.
    ///
    /// For product types, the tags will be the same, as there's only one tag.
    fn tag_range(&self) -> (u64, u64) {
        (
            self.type_tag,
            self.type_tag + (self.value_constrs.len() as u64) - 1,
        )
    }

    fn get_constr_with_tag(&self, name: &str) -> (u64, &Fields) {
        let (idx, constr) = self
            .value_constrs
            .iter()
            .enumerate()
            .find(|(_, constr)| constr.name.as_ref().map(|s| s.as_str()) == Some(name))
            .unwrap();

        (self.type_tag + idx as u64, &constr.fields)
    }
}

/// A value constructor, e.g. `Some`, `None`.
#[derive(Debug, Clone)]
struct ValCon {
    /// Name of the constructor, e.g. `True` and `False` in `Bool`.
    ///
    /// In product types, there will be only one `ValCon` and the `name` will be `None`.
    name: Option<Id>,

    /// Fields of the constructor, with names.
    ///
    /// Either all of the fields or none of them should be named.
    fields: Fields,
}

#[derive(Debug, Clone)]
enum Fields {
    Unnamed(u32),

    // NB. The vec shouldn't be empty. For nullary constructors use `Unnamed(0)`.
    Named(Vec<Id>),
}

impl Fields {
    fn is_empty(&self) -> bool {
        matches!(self, Fields::Unnamed(0))
    }

    fn find_named_field_idx(&self, name: &str) -> u64 {
        match self {
            Fields::Unnamed(_) => panic!(),
            Fields::Named(fields) => fields
                .iter()
                .enumerate()
                .find(|(_, f)| f.as_str() == name)
                .map(|(idx, _)| idx as u64)
                .unwrap(),
        }
    }
}

#[derive(Debug, Clone)]
struct Fun {
    /// Index of the function in `top_level_funs_by_idx` (if top-level function), or
    /// `associated_funs_by_idx` (if associated function).
    idx: u64,

    kind: FunKind,
}

#[derive(Debug, Clone)]
enum FunKind {
    Builtin(BuiltinFun),
    Source(ast::FunDecl),
}

impl FunKind {
    fn as_source(&self) -> &ast::FunDecl {
        match self {
            FunKind::Builtin(_) => panic!(),
            FunKind::Source(fun) => fun,
        }
    }
}
*/

/// Control flow within a function.
#[derive(Debug, Clone, Copy)]
enum ControlFlow {
    /// Continue with the next statement.
    Val(u64),

    /// Return value from the function.
    Ret(u64),

    Break(u32),

    Continue(u32),

    Unwind(u64),
}

/// Function return value.
#[derive(Debug, Clone, Copy)]
enum FunRet {
    Val(u64),
    Unwind(u64),
}

impl FunRet {
    fn into_control_flow(self) -> ControlFlow {
        match self {
            FunRet::Val(val) => ControlFlow::Val(val),
            FunRet::Unwind(val) => ControlFlow::Unwind(val),
        }
    }
}

fn val_as_i8(val: u64) -> i8 {
    val as u8 as i8
}

fn val_as_u8(val: u64) -> u8 {
    val as u8
}

fn val_as_i32(val: u64) -> i32 {
    val as u32 as i32
}

fn val_as_u32(val: u64) -> u32 {
    val as u32
}

fn i8_as_val(i: i8) -> u64 {
    i as u8 as u64
}

fn u8_as_val(i: u8) -> u64 {
    i as u64
}

fn i32_as_val(i: i32) -> u64 {
    i as u32 as u64
}

fn u32_as_val(i: u32) -> u64 {
    i as u64
}

macro_rules! val {
    ($expr:expr) => {
        match $expr {
            ControlFlow::Val(val) => val,
            ControlFlow::Ret(val) => return ControlFlow::Ret(val),
            ControlFlow::Break(n) => return ControlFlow::Break(n),
            ControlFlow::Continue(n) => return ControlFlow::Continue(n),
            ControlFlow::Unwind(val) => return ControlFlow::Unwind(val),
        }
    };
}

/*
impl Pgm {
    fn get_tag_fields(&self, tag: u64) -> &Fields {
        &self.cons_by_tag[tag as usize].fields
    }

    fn bool_alloc(&self, b: bool) -> u64 {
        if b {
            self.true_alloc
        } else {
            self.false_alloc
        }
    }

    fn tag_name_display(&self, tag: u64) -> impl std::fmt::Display + '_ {
        struct TagNameDisplay<'a> {
            ty_name: &'a Id,
            con_name: Option<&'a Id>,
        }

        impl std::fmt::Display for TagNameDisplay<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.ty_name)?;
                if let Some(con_name) = self.con_name {
                    write!(f, ".{}", con_name)?;
                }
                Ok(())
            }
        }

        let con = &self.cons_by_tag[tag as usize];

        match &con.info {
            ConInfo::Named { ty_name, con_name } => TagNameDisplay {
                ty_name,
                con_name: con_name.as_ref(),
            },
            ConInfo::Record { shape: _ } => todo!(),
            ConInfo::Variant { shape: _ } => todo!(),
        }
    }
}
*/

fn call_fun<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    fun: &Fun,
    args: Vec<u64>,
    loc: &Loc,
) -> FunRet {
    match fun {
        Fun::Builtin(builtin) => call_builtin_fun(w, pgm, heap, builtin, args, loc),
        Fun::Source(source) => call_ast_fun(w, pgm, heap, source, args, loc),
    }
}

fn call_builtin_fun<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    fun: &BuiltinFunDecl,
    args: Vec<u64>,
    loc: &Loc,
) -> FunRet {
    todo!()
}

fn call_ast_fun<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    fun: &SourceFunDecl,
    args: Vec<u64>,
    loc: &Loc,
) -> FunRet {
    assert_eq!(
        fun.params.len(),
        args.len(),
        "{}, fun: {}",
        loc_display(loc),
        fun.name.node
    );

    let mut locals: Vec<u64> = vec![0; fun.locals.len()];

    match exec(w, pgm, heap, &mut locals, &fun.body) {
        ControlFlow::Val(val) | ControlFlow::Ret(val) => FunRet::Val(val),
        ControlFlow::Break(_) | ControlFlow::Continue(_) => panic!(),
        ControlFlow::Unwind(val) => FunRet::Unwind(val),
    }
}

/*
fn call_closure<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    locals: &mut Map<Id, u64>,
    fun: u64,
    args: &[ast::CallArg],
    loc: &Loc,
) -> ControlFlow {
    match heap[fun] {
        CONSTR_TYPE_TAG => {
            let constr_tag = heap[fun + 1];
            allocate_object_from_tag(w, pgm, heap, locals, constr_tag, args)
        }

        TOP_FUN_TYPE_TAG => {
            let top_fun_idx = heap[fun + 1];
            let top_fun = &pgm.top_level_funs_by_idx[top_fun_idx as usize];
            let mut arg_values: Vec<u64> = Vec::with_capacity(args.len());
            for arg in args {
                assert!(arg.name.is_none());
                arg_values.push(val!(eval(
                    w,
                    pgm,
                    heap,
                    locals,
                    &arg.expr.node,
                    &arg.expr.loc
                )));
            }
            call_fun(w, pgm, heap, top_fun, arg_values, loc).into_control_flow()
        }

        ASSOC_FUN_TYPE_TAG => {
            let ty_tag = heap[fun + 1];
            let fun_tag = heap[fun + 2];
            let fun = &pgm.associated_funs_by_idx[ty_tag as usize][fun_tag as usize];
            let mut arg_values: Vec<u64> = Vec::with_capacity(args.len());
            for arg in args {
                arg_values.push(val!(eval(
                    w,
                    pgm,
                    heap,
                    locals,
                    &arg.expr.node,
                    &arg.expr.loc
                )));
            }
            call_fun(w, pgm, heap, fun, arg_values, loc).into_control_flow()
        }

        METHOD_TYPE_TAG => {
            let receiver = heap[fun + 1];
            let fun_idx = heap[fun + 2];
            let ty_tag = heap[receiver];
            let fun = &pgm.associated_funs_by_idx[ty_tag as usize][fun_idx as usize];
            let mut arg_values: Vec<u64> = Vec::with_capacity(args.len() + 1);
            arg_values.push(receiver);
            for arg in args {
                arg_values.push(val!(eval(
                    w,
                    pgm,
                    heap,
                    locals,
                    &arg.expr.node,
                    &arg.expr.loc
                )));
            }
            call_fun(w, pgm, heap, fun, arg_values, loc).into_control_flow()
        }

        CLOSURE_TYPE_TAG => {
            let closure_idx = heap[fun + 1];
            let closure = &pgm.closures[closure_idx as usize];

            let mut closure_locals =
                Map::with_capacity_and_hasher(closure.fvs.len(), Default::default());

            for (fv, fv_idx) in &closure.fvs {
                let fv_val = heap[fun + 2 + u64::from(*fv_idx)];
                closure_locals.insert(fv.clone(), fv_val);
            }

            for ((arg_name, _), arg_val) in closure.ast.sig.params.iter().zip(args.iter()) {
                debug_assert!(arg_val.name.is_none()); // not supported yet
                let arg_val = val!(eval(
                    w,
                    pgm,
                    heap,
                    locals,
                    &arg_val.expr.node,
                    &arg_val.expr.loc
                ));
                let old = closure_locals.insert(arg_name.clone(), arg_val);
                debug_assert!(old.is_none());
            }

            match exec(w, pgm, heap, &mut closure_locals, &closure.ast.body) {
                ControlFlow::Val(val) | ControlFlow::Ret(val) => ControlFlow::Val(val),
                ControlFlow::Break(_) | ControlFlow::Continue(_) => panic!(),
                ControlFlow::Unwind(val) => ControlFlow::Unwind(val),
            }
        }

        _ => panic!("{}: Function evaluated to non-callable", loc_display(loc)),
    }
}

/// Allocate an object from type name and optional constructor name.
fn allocate_object_from_names<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    locals: &mut Map<Id, u64>,
    ty: &Id,
    constr_name: Option<Id>,
    args: &[ast::CallArg],
    loc: &Loc,
) -> ControlFlow {
    let ty_con = pgm
        .ty_cons
        .get(ty)
        .unwrap_or_else(|| panic!("{}: Undefined type {}", loc_display(loc), ty));

    let constr_idx = match constr_name {
        Some(constr_name) => {
            let (constr_idx_, _) = ty_con
                .value_constrs
                .iter()
                .enumerate()
                .find(|(_, constr)| constr.name.as_ref() == Some(&constr_name))
                .unwrap_or_else(|| {
                    panic!(
                        "{}: Type {} does not have a constructor named {}",
                        loc_display(loc),
                        ty,
                        constr_name
                    )
                });

            constr_idx_
        }
        None => {
            assert_eq!(ty_con.value_constrs.len(), 1);
            0
        }
    };

    allocate_object_from_tag(
        w,
        pgm,
        heap,
        locals,
        ty_con.type_tag + constr_idx as u64,
        args,
    )
}

/// Allocate an object from a constructor tag and fields.
fn allocate_object_from_tag<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    locals: &mut Map<Id, u64>,
    constr_tag: u64,
    args: &[ast::CallArg],
) -> ControlFlow {
    let fields = pgm.get_tag_fields(constr_tag);
    let mut arg_values = Vec::with_capacity(args.len());

    match fields {
        Fields::Unnamed(num_fields) => {
            // Evaluate in program order and store in the same order.
            assert_eq!(*num_fields as usize, args.len());
            for arg in args {
                assert!(arg.name.is_none());
                arg_values.push(val!(eval(
                    w,
                    pgm,
                    heap,
                    locals,
                    &arg.expr.node,
                    &arg.expr.loc
                )));
            }
        }

        Fields::Named(field_names) => {
            // Evalaute in program order, store based on the order of the names
            // in the type.
            let mut named_values: Map<Id, u64> = Default::default();
            for arg in args {
                let name = arg.name.as_ref().unwrap().clone();
                let value = val!(eval(w, pgm, heap, locals, &arg.expr.node, &arg.expr.loc));
                let old = named_values.insert(name.clone(), value);
                assert!(old.is_none());
            }
            for name in field_names {
                arg_values.push(*named_values.get(name).unwrap());
            }
        }
    }

    let object = heap.allocate(1 + args.len());
    heap[object] = constr_tag;
    for (arg_idx, arg_value) in arg_values.into_iter().enumerate() {
        heap[object + 1 + (arg_idx as u64)] = arg_value;
    }

    ControlFlow::Val(object)
}
*/

fn exec<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    locals: &mut [u64],
    stmts: &[L<Stmt>],
) -> ControlFlow {
    let mut return_value: u64 = 0;

    for stmt in stmts {
        return_value = match &stmt.node {
            Stmt::Break { label: _, level } => {
                return ControlFlow::Break(*level);
            }

            Stmt::Continue { label: _, level } => {
                return ControlFlow::Continue(*level);
            }

            Stmt::Let(LetStmt { lhs, rhs }) => {
                let val = val!(eval(w, pgm, heap, locals, &rhs.node, &rhs.loc));
                if !try_bind_pat(pgm, heap, lhs, locals, val) {
                    panic!("{}: Pattern binding failed", loc_display(&stmt.loc));
                }
                val
            }

            Stmt::Assign(AssignStmt { lhs, rhs, op }) => {
                // Complex assignment operators should've been desugared during type checking.
                debug_assert_eq!(
                    *op,
                    ast::AssignOp::Eq,
                    "{}: Complex assignment: {:?}",
                    loc_display(&stmt.loc),
                    op
                );
                let rhs = val!(eval(w, pgm, heap, locals, &rhs.node, &rhs.loc));
                val!(assign(w, pgm, heap, locals, lhs, rhs))
            }

            Stmt::Expr(expr) => val!(eval(w, pgm, heap, locals, &expr.node, &expr.loc)),

            Stmt::While(WhileStmt {
                label: _,
                cond,
                body,
            }) => loop {
                let cond = val!(eval(w, pgm, heap, locals, &cond.node, &cond.loc));
                debug_assert!(cond == pgm.true_alloc || cond == pgm.false_alloc);
                if cond == pgm.false_alloc {
                    break 0; // FIXME: Return unit
                }
                match exec(w, pgm, heap, locals, body) {
                    ControlFlow::Val(_val) => {}
                    ControlFlow::Ret(val) => return ControlFlow::Ret(val),
                    ControlFlow::Break(n) => {
                        if n == 0 {
                            break 0;
                        } else {
                            return ControlFlow::Break(n - 1);
                        }
                    }
                    ControlFlow::Continue(n) => {
                        if n == 0 {
                            continue;
                        } else {
                            return ControlFlow::Continue(n - 1);
                        }
                    }
                    ControlFlow::Unwind(val) => return ControlFlow::Unwind(val),
                }
            },

            Stmt::WhileLet(WhileLetStmt {
                label: _,
                pat,
                cond,
                body,
            }) => loop {
                let val = val!(eval(w, pgm, heap, locals, &cond.node, &cond.loc));
                if !try_bind_pat(pgm, heap, pat, locals, val) {
                    break 0; // FIXME: Return unit
                }
                match exec(w, pgm, heap, locals, body) {
                    ControlFlow::Val(_val) => {}
                    ControlFlow::Ret(val) => return ControlFlow::Ret(val),
                    ControlFlow::Break(n) => {
                        if n == 0 {
                            break 0;
                        } else {
                            return ControlFlow::Break(n - 1);
                        }
                    }
                    ControlFlow::Continue(n) => {
                        if n == 0 {
                            continue;
                        } else {
                            return ControlFlow::Continue(n - 1);
                        }
                    }
                    ControlFlow::Unwind(val) => return ControlFlow::Unwind(val),
                }
            },

            Stmt::For(ForStmt {
                label: _,
                pat,
                expr,
                body,
            }) => {
                todo!()
                /*
                let iter = val!(eval(w, pgm, heap, locals, &expr.node, &expr.loc));

                let next_method = pgm.associated_funs[heap[iter] as usize]
                    .get("next@Ptr")
                    .unwrap();

                // Get the monomorphised `next` from the return type of the method.
                let iter_named_ty: &ast::NamedType = next_method
                    .kind
                    .as_source()
                    .sig
                    .return_ty
                    .as_ref()
                    .unwrap()
                    .node
                    .as_named_type();

                debug_assert!(iter_named_ty.args.is_empty());

                let option_ty_con = pgm.ty_cons.get(&iter_named_ty.name).unwrap();

                let some_tag: u64 = option_ty_con
                    .value_constrs
                    .iter()
                    .enumerate()
                    .find_map(|(idx, constr)| {
                        if constr.name == Some(SmolStr::new_static("Some")) {
                            Some(idx as u64 + option_ty_con.type_tag)
                        } else {
                            None
                        }
                    })
                    .unwrap();

                loop {
                    let next_item_option =
                        match call_fun(w, pgm, heap, next_method, vec![iter], &expr.loc) {
                            FunRet::Val(val) => val,
                            FunRet::Unwind(val) => return ControlFlow::Unwind(val),
                        };
                    if heap[next_item_option] != some_tag {
                        break;
                    }

                    let value = heap[next_item_option + 1];
                    let binds = try_bind_pat(pgm, heap, pat, value).unwrap_or_else(|| {
                        panic!(
                            "{}: For loop pattern failed to match item",
                            loc_display(&pat.loc)
                        )
                    });
                    locals.extend(binds.clone());
                    match exec(w, pgm, heap, locals, body) {
                        ControlFlow::Val(_) => {}
                        ControlFlow::Ret(val) => {
                            for var in binds.keys() {
                                locals.remove(var);
                            }
                            return ControlFlow::Ret(val);
                        }
                        ControlFlow::Break(n) => {
                            if n == 0 {
                                break;
                            } else {
                                return ControlFlow::Break(n - 1);
                            }
                        }
                        ControlFlow::Continue(n) => {
                            if n == 0 {
                                continue;
                            } else {
                                return ControlFlow::Continue(n - 1);
                            }
                        }
                        ControlFlow::Unwind(val) => {
                            for var in binds.keys() {
                                locals.remove(var);
                            }
                            return ControlFlow::Unwind(val);
                        }
                    }
                }

                0
                */
            }
        };
    }

    ControlFlow::Val(return_value)
}

fn eval<W: Write>(
    _w: &mut W,
    _pgm: &Pgm,
    _heap: &mut Heap,
    _locals: &mut [u64],
    _expr: &Expr,
    _loc: &Loc,
) -> ControlFlow {
    todo!()
    /*
    match expr {
        ast::Expr::Var(ast::VarExpr { id: var, ty_args }) => {
            debug_assert!(ty_args.is_empty());
            match locals.get(var) {
                Some(value) => ControlFlow::Val(*value),
                None => match pgm.top_level_funs.get(var) {
                    Some(top_fun) => ControlFlow::Val(heap.allocate_top_fun(top_fun.idx)),
                    None => panic!("{}: Unbound variable: {}", loc_display(loc), var),
                },
            }
        }

        ast::Expr::Constr(ast::ConstrExpr {
            id: ty_name,
            ty_args,
        }) => {
            debug_assert!(ty_args.is_empty());
            let ty_con = pgm.ty_cons.get(ty_name).unwrap();
            let ty_tag = ty_con.type_tag;
            let (first_tag, last_tag) = ty_con.tag_range();
            assert_eq!(first_tag, last_tag);
            ControlFlow::Val(heap.allocate_constr(ty_tag))
        }

        ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field }) => {
            let object = val!(eval(w, pgm, heap, locals, &object.node, &object.loc));
            let object_tag = heap[object];

            let fields = pgm.get_tag_fields(object_tag);
            match fields {
                Fields::Unnamed(_) => {}
                Fields::Named(fields) => {
                    let field_idx =
                        fields
                            .iter()
                            .enumerate()
                            .find_map(|(field_idx, field_name)| {
                                if field_name == field {
                                    Some(field_idx)
                                } else {
                                    None
                                }
                            });
                    if let Some(field_idx) = field_idx {
                        return ControlFlow::Val(heap[object + 1 + (field_idx as u64)]);
                    }
                }
            }

            panic!("{}: Unable to select field {}", loc_display(loc), field);
        }

        ast::Expr::MethodSelect(ast::MethodSelectExpr {
            object,
            object_ty: _,
            method,
            ty_args,
        }) => {
            debug_assert!(ty_args.is_empty());
            let object = val!(eval(w, pgm, heap, locals, &object.node, &object.loc));
            let object_tag = heap[object];
            match pgm.associated_funs[object_tag as usize].get(method) {
                Some(method) => ControlFlow::Val(heap.allocate_method(object, method.idx)),
                None => panic!("{}: Unable to select method {}", loc_display(loc), method),
            }
        }

        ast::Expr::ConstrSelect(ast::ConstrSelectExpr {
            ty,
            constr,
            ty_args,
        }) => {
            debug_assert!(ty_args.is_empty());
            ControlFlow::Val(constr_select(pgm, heap, ty, constr))
        }

        ast::Expr::AssocFnSelect(ast::AssocFnSelectExpr {
            ty,
            member,
            ty_args,
        }) => {
            debug_assert!(ty_args.is_empty());
            let ty_con = pgm.ty_cons.get(ty).unwrap();
            let fun = pgm.associated_funs[ty_con.type_tag as usize]
                .get(member)
                .unwrap();
            ControlFlow::Val(heap.allocate_assoc_fun(ty_con.type_tag, fun.idx))
        }

        ast::Expr::Call(ast::CallExpr { fun, args }) => {
            // See if `fun` is a method, associated function, or constructor to avoid closure
            // allocations.
            let fun: u64 = match &fun.node {
                ast::Expr::Constr(ast::ConstrExpr { id: ty, ty_args }) => {
                    debug_assert!(ty_args.is_empty());
                    return allocate_object_from_names(w, pgm, heap, locals, ty, None, args, loc);
                }

                ast::Expr::MethodSelect(ast::MethodSelectExpr {
                    object,
                    object_ty,
                    method,
                    ty_args: _,
                }) => {
                    let object = val!(eval(w, pgm, heap, locals, &object.node, &object.loc));
                    let object_tag = match object_ty.as_ref().unwrap() {
                        crate::type_checker::Ty::Con(con) => match con.as_str() {
                            "I8" => pgm.i8_ty_tag,
                            "U8" => pgm.u8_ty_tag,
                            "I32" => pgm.i32_ty_tag,
                            "U32" => pgm.u32_ty_tag,
                            _ => heap[object],
                        },
                        _ => heap[object],
                    };
                    let fun = pgm.associated_funs[object_tag as usize]
                        .get(method)
                        .unwrap_or_else(|| {
                            panic!(
                                "{}: Object with type {} (tag {}) doesn't have method {:?}",
                                loc_display(loc),
                                pgm.tag_name_display(object_tag),
                                object_tag,
                                method
                            )
                        });
                    let mut arg_vals: Vec<u64> = Vec::with_capacity(args.len() + 1);
                    arg_vals.push(object);
                    for arg in args {
                        arg_vals.push(val!(eval(
                            w,
                            pgm,
                            heap,
                            locals,
                            &arg.expr.node,
                            &arg.expr.loc
                        )));
                    }
                    return call_fun(w, pgm, heap, fun, arg_vals, loc).into_control_flow();
                }

                ast::Expr::ConstrSelect(ast::ConstrSelectExpr {
                    ty,
                    constr,
                    ty_args,
                }) => {
                    debug_assert!(ty_args.is_empty());
                    return allocate_object_from_names(
                        w,
                        pgm,
                        heap,
                        locals,
                        ty,
                        Some(constr.clone()),
                        args,
                        loc,
                    );
                }

                ast::Expr::AssocFnSelect(ast::AssocFnSelectExpr {
                    ty,
                    member,
                    ty_args,
                }) => {
                    debug_assert!(ty_args.is_empty());
                    let ty_con = pgm
                        .ty_cons
                        .get(ty)
                        .unwrap_or_else(|| panic!("{}: Undefined type: {}", loc_display(loc), ty));
                    let fun = pgm.associated_funs[ty_con.type_tag as usize]
                        .get(member)
                        .unwrap_or_else(|| {
                            panic!(
                                "{}: Type {} does not have associated function {}",
                                loc_display(loc),
                                ty,
                                member
                            )
                        });

                    let mut arg_vals: Vec<u64> = Vec::with_capacity(args.len());
                    for arg in args {
                        arg_vals.push(val!(eval(
                            w,
                            pgm,
                            heap,
                            locals,
                            &arg.expr.node,
                            &arg.expr.loc
                        )));
                    }
                    return call_fun(w, pgm, heap, fun, arg_vals, loc).into_control_flow();
                }

                _ => val!(eval(w, pgm, heap, locals, &fun.node, &fun.loc)),
            };

            // Slow path calls a closure.
            call_closure(w, pgm, heap, locals, fun, args, loc)
        }

        ast::Expr::Int(ast::IntExpr { parsed, .. }) => ControlFlow::Val(*parsed),

        ast::Expr::String(parts) => {
            let mut bytes: Vec<u8> = vec![];
            for part in parts {
                match part {
                    StringPart::Str(str) => bytes.extend(str.as_bytes()),
                    StringPart::Expr(expr) => {
                        let str = val!(eval(w, pgm, heap, locals, &expr.node, &expr.loc));
                        debug_assert_eq!(heap[str], pgm.str_ty_tag);
                        let part_bytes = heap.str_bytes(str);
                        bytes.extend(part_bytes);
                    }
                }
            }
            ControlFlow::Val(heap.allocate_str(pgm.str_ty_tag, pgm.array_u8_ty_tag, &bytes))
        }

        ast::Expr::Self_ => ControlFlow::Val(*locals.get("self").unwrap()),

        ast::Expr::BinOp(ast::BinOpExpr { left, right, op }) => {
            let left = val!(eval(w, pgm, heap, locals, &left.node, &left.loc));
            match op {
                ast::BinOp::And => {
                    if left == pgm.false_alloc {
                        return ControlFlow::Val(pgm.false_alloc);
                    }
                }
                ast::BinOp::Or => {
                    if left == pgm.true_alloc {
                        return ControlFlow::Val(pgm.true_alloc);
                    }
                }
                _ => panic!(),
            }
            eval(w, pgm, heap, locals, &right.node, &right.loc)
        }

        ast::Expr::UnOp(ast::UnOpExpr { op, expr }) => {
            let val = val!(eval(w, pgm, heap, locals, &expr.node, &expr.loc));

            match op {
                ast::UnOp::Not => {
                    debug_assert!(val == pgm.true_alloc || val == pgm.false_alloc);
                    ControlFlow::Val(pgm.bool_alloc(val == pgm.false_alloc))
                }
                ast::UnOp::Neg => {
                    panic!() // should be desugared
                }
            }
        }

        ast::Expr::Record(exprs) => {
            let shape = RecordShape::from_named_things(exprs);
            let type_tag = *pgm.record_ty_tags.get(&shape).unwrap();

            let record = heap.allocate(exprs.len() + 1);
            heap[record] = type_tag;

            if !exprs.is_empty() && exprs[0].name.is_some() {
                heap[record] = type_tag;

                let mut names: Vec<Id> = exprs
                    .iter()
                    .map(|ast::Named { name, node: _ }| name.as_ref().unwrap().clone())
                    .collect();
                names.sort();

                for (name_idx, name_) in names.iter().enumerate() {
                    let expr = exprs
                        .iter()
                        .find_map(|ast::Named { name, node }| {
                            if name.as_ref().unwrap() == name_ {
                                Some(node)
                            } else {
                                None
                            }
                        })
                        .unwrap();

                    let value = val!(eval(w, pgm, heap, locals, &expr.node, &expr.loc));
                    heap[record + (name_idx as u64) + 1] = value;
                }
            } else {
                for (idx, ast::Named { name: _, node }) in exprs.iter().enumerate() {
                    let value = val!(eval(w, pgm, heap, locals, &node.node, &node.loc));
                    heap[record + (idx as u64) + 1] = value;
                }
            }

            ControlFlow::Val(record)
        }

        ast::Expr::Variant(ast::VariantExpr { id, args }) => {
            let variant_shape = VariantShape::from_con_and_fields(id, args);
            let type_tag = *pgm.variant_ty_tags.get(&variant_shape).unwrap();
            let variant = heap.allocate(args.len() + 1);
            heap[variant] = type_tag;

            if !args.is_empty() && args[0].name.is_some() {
                let mut names: Vec<Id> = args
                    .iter()
                    .map(|ast::Named { name, node: _ }| name.as_ref().unwrap().clone())
                    .collect();
                names.sort();

                for (name_idx, name_) in names.iter().enumerate() {
                    let expr = args
                        .iter()
                        .find_map(|ast::Named { name, node }| {
                            if name.as_ref().unwrap() == name_ {
                                Some(node)
                            } else {
                                None
                            }
                        })
                        .unwrap();

                    let value = val!(eval(w, pgm, heap, locals, &expr.node, &expr.loc));
                    heap[variant + (name_idx as u64) + 1] = value;
                }
            } else {
                for (idx, ast::Named { name: _, node }) in args.iter().enumerate() {
                    let value = val!(eval(w, pgm, heap, locals, &node.node, &node.loc));
                    heap[variant + (idx as u64) + 1] = value;
                }
            }

            ControlFlow::Val(variant)
        }

        ast::Expr::Return(expr) => {
            ControlFlow::Ret(val!(eval(w, pgm, heap, locals, &expr.node, &expr.loc)))
        }

        ast::Expr::Match(ast::MatchExpr { scrutinee, alts }) => {
            let scrut = val!(eval(w, pgm, heap, locals, &scrutinee.node, &scrutinee.loc));
            for ast::Alt {
                pattern,
                guard,
                rhs,
            } in alts
            {
                assert!(guard.is_none()); // TODO
                if let Some(binds) = try_bind_pat(pgm, heap, pattern, scrut) {
                    locals.extend(binds.into_iter());
                    return exec(w, pgm, heap, locals, rhs);
                }
            }
            panic!("{}: Non-exhaustive pattern match", loc_display(loc));
        }

        ast::Expr::If(ast::IfExpr {
            branches,
            else_branch,
        }) => {
            for (cond, stmts) in branches {
                let cond = val!(eval(w, pgm, heap, locals, &cond.node, &cond.loc));
                debug_assert!(cond == pgm.true_alloc || cond == pgm.false_alloc);
                if cond == pgm.true_alloc {
                    return exec(w, pgm, heap, locals, stmts);
                }
            }
            if let Some(else_branch) = else_branch {
                return exec(w, pgm, heap, locals, else_branch);
            }
            ControlFlow::Val(0) // TODO: return unit
        }

        ast::Expr::Char(char) => {
            let alloc = heap.allocate(2);
            heap[alloc] = pgm.char_ty_tag;
            heap[alloc + 1] = u32_as_val(*char as u32);
            ControlFlow::Val(alloc)
        }

        ast::Expr::Fn(ast::FnExpr {
            sig: _,
            body: _,
            idx,
        }) => {
            let closure = &pgm.closures[*idx as usize];

            let fv_values: Vec<(u64, u32)> = closure
                .fvs
                .iter()
                .map(|(var, idx)| (*locals.get(var).unwrap(), *idx))
                .collect();

            let alloc = heap.allocate(2 + fv_values.len());
            heap[alloc] = CLOSURE_TYPE_TAG;
            heap[alloc + 1] = u32_as_val(*idx);

            for (val, idx) in fv_values {
                heap[alloc + 2 + u64::from(idx)] = val;
            }

            ControlFlow::Val(alloc)
        }
    }
    */
}

/*
fn constr_select(pgm: &Pgm, heap: &mut Heap, ty_id: &Id, constr_id: &Id) -> u64 {
    let ty_con = pgm.ty_cons.get(ty_id).unwrap();
    let (constr_idx, constr) = ty_con
        .value_constrs
        .iter()
        .enumerate()
        .find(|(_constr_idx, constr)| constr.name.as_ref().unwrap() == constr_id)
        .unwrap();
    let tag = ty_con.type_tag + (constr_idx as u64);
    let con = &pgm.cons_by_tag[tag as usize];
    debug_assert!(!constr.fields.is_empty() || con.alloc.is_some());
    con.alloc.unwrap_or_else(|| heap.allocate_constr(tag))
}
*/

fn assign<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    locals: &mut [u64],
    lhs: &L<Expr>,
    val: u64,
) -> ControlFlow {
    match &lhs.node {
        Expr::LocalVar(local_idx) => {
            locals[local_idx.as_usize()] = val;
        }

        Expr::FieldSelect(FieldSelectExpr { object, field }) => {
            let object = val!(eval(w, pgm, heap, locals, &object.node, &object.loc));
            let object_idx = heap[object];
            let object_con = pgm.cons[object_idx as usize].as_source_con();
            let object_fields = &object_con.fields;
            let field_idx = object_fields.find_named_field_idx(field);
            heap[object + 1 + (field_idx as u64)] = val;
        }

        _ => todo!("Assign statement with fancy LHS at {:?}", &lhs.loc),
    }
    ControlFlow::Val(val)
}

/*
fn try_bind_field_pats(
    pgm: &Pgm,
    heap: &mut Heap,
    constr_fields: &Fields,
    field_pats: &[ast::Named<L<ast::Pat>>],
    value: u64,
) -> Option<Map<Id, u64>> {
    let mut ret: Map<Id, u64> = Default::default();

    match constr_fields {
        Fields::Unnamed(arity) => {
            assert_eq!(
                *arity,
                field_pats.len() as u32,
                "Pattern number of fields doesn't match value number of fields"
            );
            for (field_pat_idx, field_pat) in field_pats.iter().enumerate() {
                let field_value = heap[value + (field_pat_idx as u64) + 1];
                assert!(field_pat.name.is_none());
                let map = try_bind_pat(pgm, heap, &field_pat.node, field_value)?;
                ret.extend(map.into_iter());
            }
        }

        Fields::Named(field_tys) => {
            assert_eq!(
                field_tys.len(),
                field_pats.len(),
                "Pattern number of fields doesn't match value number of fields"
            );
            for (field_idx, field_name) in field_tys.iter().enumerate() {
                let field_pat = field_pats
                    .iter()
                    .find(|field| field.name.as_ref().unwrap() == field_name)
                    .unwrap();
                let map = try_bind_pat(
                    pgm,
                    heap,
                    &field_pat.node,
                    heap[value + 1 + field_idx as u64],
                )?;
                ret.extend(map.into_iter());
            }
        }
    }

    Some(ret)
}
*/

/// Tries to match a pattern. On successful match, returns a map with variables bound in the
/// pattern. On failure returns `None`.
///
/// `heap` argument is `mut` to be able to allocate `StrView`s in string prefix patterns. In the
/// compiled version `StrView`s will be allocated on stack.
fn try_bind_pat(
    pgm: &Pgm,
    heap: &mut Heap,
    pattern: &L<Pat>,
    locals: &mut [u64],
    value: u64,
) -> bool {
    todo!()
    /*
    match &pattern.node {
        ast::Pat::Var(var) => {
            let mut map: Map<Id, u64> = Default::default();
            map.insert(var.clone(), value);
            Some(map)
        }

        ast::Pat::Ignore => Some(Default::default()),

        ast::Pat::Constr(ast::ConstrPattern {
            constr: ast::Constructor { type_, constr },
            fields: field_pats,
            ty_args: _,
        }) => {
            let value_tag = heap[value];

            let ty_con = pgm.ty_cons.get(type_).unwrap_or_else(|| {
                panic!("{}: BUG: Unknown type {}", loc_display(&pattern.loc), type_)
            });

            let (ty_con_first_tag, ty_con_last_tag) = ty_con.tag_range();

            if value_tag < ty_con_first_tag || value_tag > ty_con_last_tag {
                eprintln!("TYPE ERROR: Value type doesn't match type constructor type tag in pattern match");
                eprintln!(
                    "  value tag = {}, ty con first tag = {}, ty con last tag = {}",
                    value_tag, ty_con_first_tag, ty_con_last_tag
                );
                return None;
            }

            let constr_idx = match constr {
                Some(constr_name) => {
                    ty_con
                        .value_constrs
                        .iter()
                        .enumerate()
                        .find(|(_idx, constr)| constr_name == constr.name.as_ref().unwrap())
                        .unwrap()
                        .0
                }
                None => {
                    if ty_con_first_tag != ty_con_last_tag {
                        eprintln!("TYPE ERROR");
                        return None;
                    }
                    0
                }
            };

            if value_tag != ty_con.type_tag + (constr_idx as u64) {
                return None;
            }

            let fields = pgm.get_tag_fields(value_tag);
            try_bind_field_pats(pgm, heap, fields, field_pats, value)
        }

        ast::Pat::Record(fields) => {
            let value_tag = heap[value];
            let value_fields = pgm.get_tag_fields(value_tag);
            try_bind_field_pats(pgm, heap, value_fields, fields, value)
        }

        ast::Pat::Variant(ast::VariantPattern { constr, fields }) => {
            let value_tag = heap[value];
            let variant_shape = VariantShape::from_con_and_fields(constr, fields);
            let variant_tag = *pgm.variant_ty_tags.get(&variant_shape).unwrap();

            if value_tag != variant_tag {
                return None;
            }
            let variant_fields = pgm.get_tag_fields(variant_tag);
            try_bind_field_pats(pgm, heap, variant_fields, fields, value)
        }

        ast::Pat::Str(str) => {
            debug_assert!(heap[value] == pgm.str_ty_tag);
            let value_bytes = heap.str_bytes(value);
            if value_bytes == str.as_bytes() {
                Some(Default::default())
            } else {
                None
            }
        }

        ast::Pat::StrPfx(pfx, var) => {
            debug_assert!(heap[value] == pgm.str_ty_tag);
            let value_bytes = heap.str_bytes(value);
            if value_bytes.starts_with(pfx.as_bytes()) {
                let pfx_len = pfx.len() as u32;
                let len = heap.str_bytes(value).len() as u32;
                let rest = heap.allocate_str_view(pgm.str_ty_tag, value, pfx_len, len - pfx_len);
                let mut map: Map<Id, u64> = Default::default();
                map.insert(var.clone(), rest);
                Some(map)
            } else {
                None
            }
        }

        ast::Pat::Or(pat1, pat2) => {
            if let Some(binds) = try_bind_pat(pgm, heap, pat1, value) {
                return Some(binds);
            }
            if let Some(binds) = try_bind_pat(pgm, heap, pat2, value) {
                return Some(binds);
            }
            None
        }

        ast::Pat::Char(char) => {
            debug_assert_eq!(heap[value], pgm.char_ty_tag);
            if heap[value + 1] == u64::from(*char as u32) {
                Some(Default::default())
            } else {
                None
            }
        }
    }
    */
}

/*
fn obj_to_string(pgm: &Pgm, heap: &Heap, obj: u64, loc: &Loc) -> String {
    use std::fmt::Write;

    let mut s = String::new();

    let tag = heap[obj];
    let con = &pgm.cons_by_tag[tag as usize];

    write!(&mut s, "{}: ", loc_display(loc)).unwrap();

    match &con.info {
        ConInfo::Named {
            ty_name,
            con_name: Some(con_name),
        } => write!(&mut s, "{}.{}", ty_name, con_name).unwrap(),

        ConInfo::Named {
            ty_name,
            con_name: None,
        } => write!(&mut s, "{}", ty_name).unwrap(),

        ConInfo::Record { .. } => {}

        ConInfo::Variant { .. } => {}
    }

    write!(&mut s, "(").unwrap();

    match &con.fields {
        Fields::Unnamed(arity) => {
            for i in 0..*arity {
                write!(&mut s, "{}", heap[obj + 1 + u64::from(i)]).unwrap();
                if i != arity - 1 {
                    write!(&mut s, ", ").unwrap();
                }
            }
        }
        Fields::Named(fields) => {
            for (i, field_name) in fields.iter().enumerate() {
                write!(&mut s, "{} = {}", field_name, heap[obj + 1 + (i as u64)]).unwrap();
                if i != fields.len() - 1 {
                    write!(&mut s, ", ").unwrap();
                }
            }
        }
    }

    write!(&mut s, ")").unwrap();

    s
}
*/
