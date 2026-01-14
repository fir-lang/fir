#![allow(clippy::needless_range_loop, clippy::too_many_arguments)]

const INITIAL_HEAP_SIZE_WORDS: usize = (1024 * 1024 * 1024) / 8; // 1 GiB

mod heap;

use heap::Heap;

use crate::ast::{self, Id, L, Loc};
use crate::lowering::*;
use crate::utils::loc_display;

use std::cmp::Ordering;
use std::io::Write;
use std::ops::{Neg, Rem};

// Just lowered program with some extra cached stuff for easy access.
struct Pgm {
    funs: Vec<Fun>,
    closures: Vec<Closure>,
    cli_args: Vec<String>,

    /// Indexed by `HeapObjIdx`. Allocations of nullary constructors.
    allocs: Vec<u64>,

    // Some allocations and type tags for the built-ins.
    true_alloc: u64,
    false_alloc: u64,
    ordering_less_alloc: u64,
    ordering_equal_alloc: u64,
    ordering_greater_alloc: u64,
    unit_alloc: u64,
    char_con_idx: HeapObjIdx,
    str_con_idx: HeapObjIdx,
}

/// A call stack frame.
struct Frame {
    call_site: Loc,
    kind: FrameKind,
}

enum FrameKind {
    Builtin(BuiltinFunDecl),
    Source(Id),
    Closure(Loc),
}

impl Pgm {
    fn init(lowered_pgm: LoweredPgm, heap: &mut Heap, cli_args: Vec<String>) -> Pgm {
        let LoweredPgm {
            heap_objs,
            funs,
            closures,
            true_con_idx,
            false_con_idx,
            char_con_idx,
            ordering_less_con_idx,
            ordering_equal_con_idx,
            ordering_greater_con_idx,
            str_con_idx,
            unit_con_idx,
        } = lowered_pgm;

        let mut allocs: Vec<u64> = vec![u64::MAX; heap_objs.len()];

        // Allocate singletons for constructors without fields.
        for (i, heap_obj) in heap_objs.iter().enumerate() {
            match heap_obj {
                HeapObj::Builtin(_) => continue,

                HeapObj::Source(source_con) => {
                    if source_con.fields.is_empty() {
                        debug_assert_eq!(i, source_con.idx.as_usize());
                        allocs[i] = heap.allocate_tag(i as u64);
                    }
                }

                HeapObj::Record(record) => {
                    if record.fields.is_empty() {
                        allocs[i] = heap.allocate_tag(i as u64);
                    }
                }
            }
        }

        let true_alloc = allocs[true_con_idx.as_usize()];
        let false_alloc = allocs[false_con_idx.as_usize()];
        let ordering_less_alloc = allocs[ordering_less_con_idx.as_usize()];
        let ordering_equal_alloc = allocs[ordering_equal_con_idx.as_usize()];
        let ordering_greater_alloc = allocs[ordering_greater_con_idx.as_usize()];
        let unit_alloc = allocs[unit_con_idx.as_usize()];

        Pgm {
            funs,
            closures,
            cli_args,
            allocs,
            true_alloc,
            false_alloc,
            ordering_less_alloc,
            ordering_equal_alloc,
            ordering_greater_alloc,
            unit_alloc,
            char_con_idx,
            str_con_idx,
        }
    }
}

/// Run the program, passing the arguments `args` as the `Array[Str]` argument to `main`.
pub fn run_with_args<W: Write>(w: &mut W, pgm: LoweredPgm, main: &str, args: Vec<String>) {
    let mut heap = Heap::new();
    let pgm = Pgm::init(pgm, &mut heap, args);

    let main_fun: &SourceFunDecl = pgm
        .funs
        .iter()
        .find_map(|fun| match fun {
            Fun::Source(fun @ SourceFunDecl { name, .. }) if name.node.as_str() == main => {
                Some(fun)
            }
            _ => None,
        })
        .unwrap_or_else(|| panic!("Main function `{main}` is not defined"));

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

    // Note: normally `call_fun` adjusts the stack, but when calling `main` we don't call
    // `call_fun`, so we add `main` here.
    let mut call_stack = vec![Frame {
        kind: FrameKind::Source(main_fun.name.node.clone()),
        call_site: Loc::dummy(),
    }];

    let ret = call_ast_fun(
        w,
        &pgm,
        &mut heap,
        main_fun,
        vec![],
        &call_loc,
        &mut call_stack,
    );

    match ret {
        FunRet::Val(_val) => {
            // Note: This does not hold because apparently we weren't too careful with how we return
            // units. So far we never needed to check or use a unit return, so it was fine. If we
            // want this assertion we should fix unit returning statements and expressions.
            // debug_assert_eq!(_val, pgm.unit_alloc);
        }
        FunRet::Unwind(_) => {
            // TODO: We should show at least the object here somehow, but ideally also the
            // location/stack trace of the code throwing exception.
            panic!("Uncaught exception");
        }
    }
}

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

fn val_as_i64(val: u64) -> i64 {
    val as i64
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

fn call_fun<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    fun: &Fun,
    args: Vec<u64>,
    loc: &Loc,
    call_stack: &mut Vec<Frame>,
) -> FunRet {
    let ret = match fun {
        Fun::Builtin(builtin) => {
            call_stack.push(Frame {
                call_site: loc.clone(),
                kind: FrameKind::Builtin(builtin.clone()),
            });
            call_builtin_fun(w, pgm, heap, builtin, args, loc, call_stack)
        }
        Fun::Source(source) => {
            call_stack.push(Frame {
                call_site: loc.clone(),
                kind: FrameKind::Source(source.name.node.clone()),
            });
            call_ast_fun(w, pgm, heap, source, args, loc, call_stack)
        }
    };
    call_stack.pop();
    ret
}

fn call_ast_fun<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    fun: &SourceFunDecl,
    args: Vec<u64>,
    loc: &Loc,
    call_stack: &mut Vec<Frame>,
) -> FunRet {
    debug_assert_eq!(
        fun.params.len(),
        args.len(),
        "{}, fun: {}",
        loc_display(loc),
        fun.name.node
    );

    let mut locals = args;
    locals.resize(fun.locals.len(), 0);

    match exec(w, pgm, heap, &mut locals, &fun.body, call_stack) {
        ControlFlow::Val(val) | ControlFlow::Ret(val) => FunRet::Val(val),
        ControlFlow::Break(_) | ControlFlow::Continue(_) => panic!(),
        ControlFlow::Unwind(val) => FunRet::Unwind(val),
    }
}

fn call_closure<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    locals: &mut [u64],
    fun: u64,
    args: &[L<Expr>],
    loc: &Loc,
    call_stack: &mut Vec<Frame>,
) -> ControlFlow {
    match HeapObjIdx(heap[fun] as u32) {
        CON_CON_IDX => {
            let con_idx = HeapObjIdx(heap[fun + 1] as u32);
            allocate_object_from_idx(w, pgm, heap, locals, con_idx, args, call_stack)
        }

        FUN_CON_IDX => {
            let top_fun_idx = heap[fun + 1];
            let fun = &pgm.funs[top_fun_idx as usize];
            let mut arg_values: Vec<u64> = Vec::with_capacity(args.len());
            for arg in args {
                arg_values.push(val!(eval(
                    w, pgm, heap, locals, &arg.node, &arg.loc, call_stack
                )));
            }
            call_fun(w, pgm, heap, fun, arg_values, loc, call_stack).into_control_flow()
        }

        CLOSURE_CON_IDX => {
            let closure_idx = heap[fun + 1];
            let closure = &pgm.closures[closure_idx as usize];

            let mut closure_locals: Vec<u64> = vec![0; closure.locals.len()];

            // Load closure's free variables into locals.
            for (i, fv) in closure.fvs.iter().enumerate() {
                let fv_value = heap[fun + 2 + (i as u64)];
                closure_locals[fv.use_idx.as_usize()] = fv_value;
            }

            // Copy closure arguments into locals.
            debug_assert_eq!(args.len(), closure.params.len());

            for (i, arg) in args.iter().enumerate() {
                let arg_val = val!(eval(w, pgm, heap, locals, &arg.node, &arg.loc, call_stack));
                closure_locals[i] = arg_val;
            }

            call_stack.push(Frame {
                call_site: loc.clone(),
                kind: FrameKind::Closure(closure.loc.clone()),
            });

            let ret = match exec(w, pgm, heap, &mut closure_locals, &closure.body, call_stack) {
                ControlFlow::Val(val) | ControlFlow::Ret(val) => ControlFlow::Val(val),
                ControlFlow::Break(_) | ControlFlow::Continue(_) => panic!(),
                ControlFlow::Unwind(val) => ControlFlow::Unwind(val),
            };

            call_stack.pop();

            ret
        }

        _ => panic!("{}: Function evaluated to non-callable", loc_display(loc)),
    }
}

/// Allocate an object from a con idx and fields.
fn allocate_object_from_idx<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    locals: &mut [u64],
    con_idx: HeapObjIdx,
    args: &[L<Expr>],
    call_stack: &mut Vec<Frame>,
) -> ControlFlow {
    let object = heap.allocate(1 + args.len());
    heap[object] = con_idx.as_u64();
    for (arg_idx, arg) in args.iter().enumerate() {
        let val = val!(eval(w, pgm, heap, locals, &arg.node, &arg.loc, call_stack));
        heap[object + 1 + (arg_idx as u64)] = val;
    }
    ControlFlow::Val(object)
}

fn exec<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    locals: &mut [u64],
    stmts: &[L<Stmt>],
    call_stack: &mut Vec<Frame>,
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
                let val = val!(eval(w, pgm, heap, locals, &rhs.node, &rhs.loc, call_stack));
                if !try_bind_pat(pgm, heap, lhs, locals, val) {
                    panic!("{}: Pattern binding failed", loc_display(&stmt.loc));
                }
                val
            }

            Stmt::Assign(AssignStmt { lhs, rhs }) => {
                let rhs = val!(eval(w, pgm, heap, locals, &rhs.node, &rhs.loc, call_stack));
                val!(assign(w, pgm, heap, locals, lhs, rhs, call_stack))
            }

            Stmt::Expr(expr) => val!(eval(
                w, pgm, heap, locals, &expr.node, &expr.loc, call_stack
            )),

            Stmt::While(WhileStmt {
                label: _,
                cond,
                body,
            }) => loop {
                let cond = val!(eval(
                    w, pgm, heap, locals, &cond.node, &cond.loc, call_stack
                ));
                debug_assert!(cond == pgm.true_alloc || cond == pgm.false_alloc);
                if cond == pgm.false_alloc {
                    break 0; // FIXME: Return unit
                }
                match exec(w, pgm, heap, locals, body, call_stack) {
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
        };
    }

    ControlFlow::Val(return_value)
}

fn eval<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    locals: &mut [u64],
    expr: &Expr,
    loc: &Loc,
    call_stack: &mut Vec<Frame>,
) -> ControlFlow {
    match expr {
        Expr::LocalVar(local_idx) => ControlFlow::Val(locals[local_idx.as_usize()]),

        Expr::Fun(fun_idx) => ControlFlow::Val(heap.allocate_fun(fun_idx.as_u64())),

        Expr::Con(con_idx) => ControlFlow::Val(heap.allocate_con(con_idx.as_u64())),

        Expr::ConAlloc(con_idx, args) => {
            if args.is_empty() {
                ControlFlow::Val(pgm.allocs[con_idx.as_usize()])
            } else {
                allocate_object_from_idx(w, pgm, heap, locals, *con_idx, args, call_stack)
            }
        }

        Expr::FieldSel(FieldSelExpr {
            object,
            field: _,
            idx,
        }) => {
            let object = val!(eval(
                w,
                pgm,
                heap,
                locals,
                &object.node,
                &object.loc,
                call_stack
            ));
            ControlFlow::Val(heap[object + 1 + (*idx as u64)])
        }

        Expr::Call(CallExpr { fun, args }) => {
            // See if `fun` is a method, associated function, or constructor to avoid closure
            // allocations.
            let fun: u64 = match &fun.node {
                Expr::Con(con_idx) => {
                    return allocate_object_from_idx(
                        w, pgm, heap, locals, *con_idx, args, call_stack,
                    );
                }

                Expr::Fun(fun_idx) => {
                    let mut arg_vals: Vec<u64> = Vec::with_capacity(args.len());
                    for arg in args {
                        arg_vals.push(val!(eval(
                            w, pgm, heap, locals, &arg.node, &arg.loc, call_stack
                        )));
                    }
                    let fun = &pgm.funs[fun_idx.as_usize()];
                    return call_fun(w, pgm, heap, fun, arg_vals, loc, call_stack)
                        .into_control_flow();
                }

                _ => val!(eval(w, pgm, heap, locals, &fun.node, &fun.loc, call_stack)),
            };

            // Slow path calls a closure.
            call_closure(w, pgm, heap, locals, fun, args, loc, call_stack)
        }

        Expr::Int(int) => ControlFlow::Val(*int),

        Expr::Str(str) => {
            ControlFlow::Val(heap.allocate_str(pgm.str_con_idx.as_u64(), Repr::U8, str.as_bytes()))
        }

        Expr::BoolAnd(left, right) => {
            let left = val!(eval(
                w, pgm, heap, locals, &left.node, &left.loc, call_stack
            ));
            if left == pgm.false_alloc {
                ControlFlow::Val(pgm.false_alloc)
            } else {
                eval(w, pgm, heap, locals, &right.node, &right.loc, call_stack)
            }
        }

        Expr::BoolOr(left, right) => {
            let left = val!(eval(
                w, pgm, heap, locals, &left.node, &left.loc, call_stack
            ));
            if left == pgm.true_alloc {
                ControlFlow::Val(pgm.true_alloc)
            } else {
                eval(w, pgm, heap, locals, &right.node, &right.loc, call_stack)
            }
        }

        Expr::Return(expr) => ControlFlow::Ret(val!(eval(
            w, pgm, heap, locals, &expr.node, &expr.loc, call_stack
        ))),

        Expr::Match(MatchExpr { scrutinee, alts }) => {
            let scrut = val!(eval(
                w,
                pgm,
                heap,
                locals,
                &scrutinee.node,
                &scrutinee.loc,
                call_stack
            ));
            for Alt { pat, guard, rhs } in alts {
                if try_bind_pat(pgm, heap, pat, locals, scrut) {
                    if let Some(guard) = guard {
                        let guard = val!(eval(
                            w,
                            pgm,
                            heap,
                            locals,
                            &guard.node,
                            &guard.loc,
                            call_stack
                        ));
                        if guard == pgm.true_alloc {
                            return exec(w, pgm, heap, locals, rhs, call_stack);
                        } else {
                            continue;
                        }
                    }
                    return exec(w, pgm, heap, locals, rhs, call_stack);
                }
            }
            panic!("{}: Non-exhaustive pattern match", loc_display(loc));
        }

        Expr::If(IfExpr {
            branches,
            else_branch,
        }) => {
            for (cond, stmts) in branches {
                let cond = val!(eval(
                    w, pgm, heap, locals, &cond.node, &cond.loc, call_stack
                ));
                debug_assert!(cond == pgm.true_alloc || cond == pgm.false_alloc);
                if cond == pgm.true_alloc {
                    return exec(w, pgm, heap, locals, stmts, call_stack);
                }
            }
            if let Some(else_branch) = else_branch {
                return exec(w, pgm, heap, locals, else_branch, call_stack);
            }
            ControlFlow::Val(pgm.unit_alloc)
        }

        Expr::ClosureAlloc(closure_idx) => {
            let closure = &pgm.closures[closure_idx.as_usize()];
            let alloc = heap.allocate(2 + closure.fvs.len());
            heap[alloc] = CLOSURE_CON_IDX.as_u64();
            heap[alloc + 1] = closure_idx.as_u64();

            for (fv_idx, fv) in closure.fvs.iter().enumerate() {
                heap[alloc + 2 + (fv_idx as u64)] = locals[fv.alloc_idx.as_usize()];
            }

            ControlFlow::Val(alloc)
        }

        Expr::Is(IsExpr { expr, pat }) => {
            let val = val!(eval(
                w, pgm, heap, locals, &expr.node, &expr.loc, call_stack
            ));
            ControlFlow::Val(if try_bind_pat(pgm, heap, pat, locals, val) {
                pgm.true_alloc
            } else {
                pgm.false_alloc
            })
        }

        Expr::Do(stmts) => exec(w, pgm, heap, locals, stmts, call_stack),

        Expr::Variant(expr) => {
            // Note: the interpreter can only deal with variants of boxed types. If `expr` is an
            // unboxed type things will go wrong.
            //
            // We can't check expr types here, so we just assume that `expr` doesn't evaluate to an
            // unboxed value, without checking.
            //
            // It should be checked in an earlier pass that the `expr` here is not a value type.
            //
            // Also note: currently the only value types are integer types.
            eval(w, pgm, heap, locals, &expr.node, &expr.loc, call_stack)
        }
    }
}

fn assign<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    locals: &mut [u64],
    lhs: &L<Expr>,
    val: u64,
    call_stack: &mut Vec<Frame>,
) -> ControlFlow {
    match &lhs.node {
        Expr::LocalVar(local_idx) => {
            locals[local_idx.as_usize()] = val;
        }

        Expr::FieldSel(FieldSelExpr {
            object,
            field: _,
            idx,
        }) => {
            let object = val!(eval(
                w,
                pgm,
                heap,
                locals,
                &object.node,
                &object.loc,
                call_stack,
            ));
            heap[object + 1 + (*idx as u64)] = val;
        }

        _ => todo!("Assign statement with fancy LHS at {:?}", &lhs.loc),
    }
    ControlFlow::Val(pgm.unit_alloc)
}

/// Tries to match a pattern. On successful match, returns a map with variables bound in the
/// pattern. On failure returns `None`.
///
/// `heap` argument is `mut` to be able to allocate `StrView`s in string prefix patterns. In the
/// compiled version `StrView`s will be allocated on stack.
fn try_bind_pat(pgm: &Pgm, heap: &mut Heap, pat: &L<Pat>, locals: &mut [u64], value: u64) -> bool {
    match &pat.node {
        Pat::Var(var) => {
            locals[var.as_usize()] = value;
            true
        }

        Pat::Ignore => true,

        Pat::Str(str) => {
            if heap[value] != pgm.str_con_idx.as_u64() {
                return false;
            }
            let value_bytes = heap.str_bytes(value);
            value_bytes == str.as_bytes()
        }

        Pat::Char(char) => {
            if heap[value] != pgm.char_con_idx.as_u64() {
                return false;
            }
            heap[value + 1] == u64::from(*char as u32)
        }

        Pat::Or(pat1, pat2) => {
            try_bind_pat(pgm, heap, pat1, locals, value)
                || try_bind_pat(pgm, heap, pat2, locals, value)
        }

        Pat::Con(ConPat {
            con: con_idx,
            fields: field_pats,
        }) => {
            let value_tag = heap[value];
            if value_tag != con_idx.as_u64() {
                return false;
            }

            for (field_idx, field_pat) in field_pats.iter().enumerate() {
                let field_value = heap[value + 1 + (field_idx as u64)];
                if !try_bind_pat(pgm, heap, field_pat, locals, field_value) {
                    return false;
                }
            }

            true
        }

        Pat::Variant(p) => {
            // `p` needs to match a boxed type, but we can't check this here (e.g. in an `assert`).
            // See the documentation in `Expr::Variant` evaluator.
            try_bind_pat(pgm, heap, p, locals, value)
        }
    }
}

fn call_builtin_fun<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    fun: &BuiltinFunDecl,
    args: Vec<u64>,
    loc: &Loc,
    call_stack: &mut Vec<Frame>,
) -> FunRet {
    match fun {
        BuiltinFunDecl::Panic => {
            debug_assert_eq!(args.len(), 1);
            let msg = args[0];
            let bytes = heap.str_bytes(msg);
            let msg = String::from_utf8_lossy(bytes).into_owned();
            let mut msg_str = format!("{}: PANIC: {}\n", loc_display(loc), msg);
            msg_str.push_str("\nFIR STACK:\n");
            write_call_stack(call_stack, &mut msg_str);
            panic!("{}", msg_str);
        }

        BuiltinFunDecl::PrintStrNoNl => {
            debug_assert_eq!(args.len(), 1);
            let str = args[0];
            debug_assert_eq!(heap[str], pgm.str_con_idx.as_u64());
            let bytes = heap.str_bytes(str);
            write!(w, "{}", String::from_utf8_lossy(bytes)).unwrap();
            FunRet::Val(pgm.unit_alloc)
        }

        BuiltinFunDecl::ShrI8 => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(i8_as_val(val_as_i8(i1) >> val_as_i8(i2)))
        }

        BuiltinFunDecl::ShrU8 => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(u8_as_val(val_as_u8(i1) >> val_as_u8(i2)))
        }

        BuiltinFunDecl::ShrI32 => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(i32_as_val(val_as_i32(i1) >> val_as_i32(i2)))
        }

        BuiltinFunDecl::ShrU32 => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(u32_as_val(val_as_u32(i1) >> val_as_u32(i2)))
        }

        BuiltinFunDecl::BitAndI8 => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(i8_as_val(val_as_i8(i1) & val_as_i8(i2)))
        }

        BuiltinFunDecl::BitAndU8 => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(u8_as_val(val_as_u8(i1) & val_as_u8(i2)))
        }

        BuiltinFunDecl::BitAndI32 => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(i32_as_val(val_as_i32(i1) & val_as_i32(i2)))
        }

        BuiltinFunDecl::BitAndU32 => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(u32_as_val(val_as_u32(i1) & val_as_u32(i2)))
        }

        BuiltinFunDecl::BitOrI8 => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(i8_as_val(val_as_i8(i1) | val_as_i8(i2)))
        }

        BuiltinFunDecl::BitOrU8 => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(u8_as_val(val_as_u8(i1) | val_as_u8(i2)))
        }

        BuiltinFunDecl::BitOrI32 => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(i32_as_val(val_as_i32(i1) | val_as_i32(i2)))
        }

        BuiltinFunDecl::BitOrU32 => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(u32_as_val(val_as_u32(i1) | val_as_u32(i2)))
        }

        BuiltinFunDecl::BitXorU32 => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(u32_as_val(val_as_u32(i1) ^ val_as_u32(i2)))
        }

        BuiltinFunDecl::U32Mod => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            if i2 == 0 {
                panic!("{}: Div by zero", loc_display(loc));
            }
            FunRet::Val(u32_as_val(val_as_u32(i1) % val_as_u32(i2)))
        }

        BuiltinFunDecl::ToStrI8 => {
            debug_assert_eq!(args.len(), 1);
            let i = args[0];
            FunRet::Val(heap.allocate_str(
                pgm.str_con_idx.as_u64(),
                Repr::U8,
                format!("{}", val_as_i8(i)).as_bytes(),
            ))
        }

        BuiltinFunDecl::ToStrU8 => {
            debug_assert_eq!(args.len(), 1);
            let i = args[0];
            FunRet::Val(heap.allocate_str(
                pgm.str_con_idx.as_u64(),
                Repr::U8,
                format!("{}", val_as_u8(i)).as_bytes(),
            ))
        }

        BuiltinFunDecl::ToStrI32 => {
            debug_assert_eq!(args.len(), 1);
            let i = args[0];
            FunRet::Val(heap.allocate_str(
                pgm.str_con_idx.as_u64(),
                Repr::U8,
                format!("{}", val_as_i32(i)).as_bytes(),
            ))
        }

        BuiltinFunDecl::ToStrU32 => {
            debug_assert_eq!(args.len(), 1);
            let i = args[0];
            FunRet::Val(heap.allocate_str(
                pgm.str_con_idx.as_u64(),
                Repr::U8,
                format!("{}", val_as_u32(i)).as_bytes(),
            ))
        }

        BuiltinFunDecl::ToStrI64 => {
            debug_assert_eq!(args.len(), 1);
            let i = val_as_i64(args[0]);
            FunRet::Val(heap.allocate_str(
                pgm.str_con_idx.as_u64(),
                Repr::U8,
                format!("{}", i).as_bytes(),
            ))
        }

        BuiltinFunDecl::ToStrU64 => {
            debug_assert_eq!(args.len(), 1);
            let i = args[0];
            FunRet::Val(heap.allocate_str(
                pgm.str_con_idx.as_u64(),
                Repr::U8,
                format!("{}", i).as_bytes(),
            ))
        }

        BuiltinFunDecl::U8AsI8 => {
            debug_assert_eq!(args.len(), 1);
            FunRet::Val(i8_as_val(val_as_u8(args[0]) as i8))
        }

        BuiltinFunDecl::U8AsU32 => {
            debug_assert_eq!(args.len(), 1);
            FunRet::Val(u32_as_val(val_as_u8(args[0]) as u32))
        }

        BuiltinFunDecl::U32AsU8 => {
            debug_assert_eq!(args.len(), 1);
            FunRet::Val(u8_as_val(val_as_u32(args[0]) as u8))
        }

        BuiltinFunDecl::U32AsI32 => {
            debug_assert_eq!(args.len(), 1);
            FunRet::Val(i32_as_val(val_as_u32(args[0]) as i32))
        }

        BuiltinFunDecl::U32AsU64 => {
            debug_assert_eq!(args.len(), 1);
            FunRet::Val(val_as_u32(args[0]) as u64)
        }

        BuiltinFunDecl::I8Shl => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(i8_as_val(val_as_i8(i1) << val_as_i8(i2)))
        }

        BuiltinFunDecl::U8Shl => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(u8_as_val(val_as_u8(i1) << val_as_u8(i2)))
        }

        BuiltinFunDecl::I32Shl => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(i32_as_val(val_as_i32(i1) << val_as_i32(i2)))
        }

        BuiltinFunDecl::U32Shl => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(u32_as_val(val_as_u32(i1) << val_as_u32(i2)))
        }

        BuiltinFunDecl::I8Rem => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(i8_as_val(val_as_i8(i1).rem(val_as_i8(i2))))
        }

        BuiltinFunDecl::U8Rem => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(u8_as_val(val_as_u8(i1).rem(val_as_u8(i2))))
        }

        BuiltinFunDecl::I32Rem => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(i32_as_val(val_as_i32(i1).rem(val_as_i32(i2))))
        }

        BuiltinFunDecl::U32Rem => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(u32_as_val(val_as_u32(i1).rem(val_as_u32(i2))))
        }

        BuiltinFunDecl::I8Cmp => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            let ordering = match val_as_i8(i1).cmp(&val_as_i8(i2)) {
                Ordering::Less => pgm.ordering_less_alloc,
                Ordering::Equal => pgm.ordering_equal_alloc,
                Ordering::Greater => pgm.ordering_greater_alloc,
            };

            FunRet::Val(ordering)
        }

        BuiltinFunDecl::U8Cmp => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            let ordering = match val_as_u8(i1).cmp(&val_as_u8(i2)) {
                Ordering::Less => pgm.ordering_less_alloc,
                Ordering::Equal => pgm.ordering_equal_alloc,
                Ordering::Greater => pgm.ordering_greater_alloc,
            };

            FunRet::Val(ordering)
        }

        BuiltinFunDecl::I32Cmp => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            let ordering = match val_as_i32(i1).cmp(&val_as_i32(i2)) {
                Ordering::Less => pgm.ordering_less_alloc,
                Ordering::Equal => pgm.ordering_equal_alloc,
                Ordering::Greater => pgm.ordering_greater_alloc,
            };

            FunRet::Val(ordering)
        }

        BuiltinFunDecl::U32Cmp => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            let ordering = match val_as_u32(i1).cmp(&val_as_u32(i2)) {
                Ordering::Less => pgm.ordering_less_alloc,
                Ordering::Equal => pgm.ordering_equal_alloc,
                Ordering::Greater => pgm.ordering_greater_alloc,
            };

            FunRet::Val(ordering)
        }

        BuiltinFunDecl::U64Cmp => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            let ordering = match i1.cmp(&i2) {
                Ordering::Less => pgm.ordering_less_alloc,
                Ordering::Equal => pgm.ordering_equal_alloc,
                Ordering::Greater => pgm.ordering_greater_alloc,
            };

            FunRet::Val(ordering)
        }

        BuiltinFunDecl::I8Add => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(i8_as_val(val_as_i8(i1) + val_as_i8(i2)))
        }

        BuiltinFunDecl::U8Add => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(u8_as_val(val_as_u8(i1) + val_as_u8(i2)))
        }

        BuiltinFunDecl::I32Add => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(i32_as_val(val_as_i32(i1) + val_as_i32(i2)))
        }

        BuiltinFunDecl::U32Add => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(u32_as_val(val_as_u32(i1) + val_as_u32(i2)))
        }

        BuiltinFunDecl::U64Add => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(i1 + i2)
        }

        BuiltinFunDecl::I8Sub => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(i8_as_val(val_as_i8(i1) - val_as_i8(i2)))
        }

        BuiltinFunDecl::U8Sub => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(u8_as_val(val_as_u8(i1) - val_as_u8(i2)))
        }

        BuiltinFunDecl::I32Sub => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(i32_as_val(val_as_i32(i1) - val_as_i32(i2)))
        }

        BuiltinFunDecl::U32Sub => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(u32_as_val(val_as_u32(i1) - val_as_u32(i2)))
        }

        BuiltinFunDecl::I8Mul => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(i8_as_val(val_as_i8(i1).overflowing_mul(val_as_i8(i2)).0))
        }

        BuiltinFunDecl::U8Mul => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(u8_as_val(val_as_u8(i1).overflowing_mul(val_as_u8(i2)).0))
        }

        BuiltinFunDecl::I32Mul => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(i32_as_val(val_as_i32(i1).overflowing_mul(val_as_i32(i2)).0))
        }

        BuiltinFunDecl::U32Mul => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(u32_as_val(val_as_u32(i1).overflowing_mul(val_as_u32(i2)).0))
        }

        BuiltinFunDecl::U64Mul => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(i1.overflowing_mul(i2).0)
        }

        BuiltinFunDecl::I8Div => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(i8_as_val(val_as_i8(i1) / val_as_i8(i2)))
        }

        BuiltinFunDecl::U8Div => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(u8_as_val(val_as_u8(i1) / val_as_u8(i2)))
        }

        BuiltinFunDecl::I32Div => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(i32_as_val(val_as_i32(i1) / val_as_i32(i2)))
        }

        BuiltinFunDecl::U32Div => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            FunRet::Val(u32_as_val(val_as_u32(i1) / val_as_u32(i2)))
        }

        BuiltinFunDecl::I8Eq
        | BuiltinFunDecl::U8Eq
        | BuiltinFunDecl::I32Eq
        | BuiltinFunDecl::U32Eq => {
            debug_assert_eq!(args.len(), 2);
            let u1 = args[0];
            let u2 = args[1];
            FunRet::Val(if u1 == u2 {
                pgm.true_alloc
            } else {
                pgm.false_alloc
            })
        }

        BuiltinFunDecl::I32AsU32 => {
            debug_assert_eq!(args.len(), 1);
            FunRet::Val(u32_as_val(val_as_i32(args[0]) as u32))
        }

        BuiltinFunDecl::I32Abs => {
            debug_assert_eq!(args.len(), 1);
            FunRet::Val(i32_as_val(val_as_i32(args[0]).abs()))
        }

        BuiltinFunDecl::I8Neg => {
            debug_assert_eq!(args.len(), 1);
            FunRet::Val(i8_as_val(val_as_i8(args[0]).neg()))
        }

        BuiltinFunDecl::I32Neg => {
            debug_assert_eq!(args.len(), 1);
            FunRet::Val(i32_as_val(val_as_i32(args[0]).neg()))
        }

        BuiltinFunDecl::ThrowUnchecked => {
            debug_assert_eq!(args.len(), 1);
            let exn = args[0];
            FunRet::Unwind(exn)
        }

        BuiltinFunDecl::Try {
            ok_con, err_con, ..
        } => {
            debug_assert_eq!(args.len(), 1);
            let cb = args[0];

            // NB. No need to pass locals here as locals are used to evaluate closure arguments, and
            // we don't pass any arguments.
            let (val, con_idx) = match call_closure(w, pgm, heap, &mut [], cb, &[], loc, call_stack)
            {
                ControlFlow::Val(val) => (val, *ok_con),
                ControlFlow::Unwind(val) => (val, *err_con),
                ControlFlow::Break(_) | ControlFlow::Continue(_) | ControlFlow::Ret(_) => panic!(),
            };

            let object = heap.allocate(1 + args.len());
            heap[object] = con_idx.as_u64();
            heap[object + 1] = val;
            FunRet::Val(object)
        }

        BuiltinFunDecl::ArrayNew { t } => {
            debug_assert_eq!(args.len(), 1);
            let cap = val_as_u32(args[0]);
            let repr = Repr::from_mono_ty(t);
            FunRet::Val(heap.allocate_array(repr, cap))
        }

        BuiltinFunDecl::ArraySlice { t: _ } => {
            debug_assert_eq!(args.len(), 3); // array, start, end
            let array = args[0];
            let start = val_as_u32(args[1]);
            let end = val_as_u32(args[2]);
            FunRet::Val(heap.array_slice(array, start, end, loc, call_stack))
        }

        BuiltinFunDecl::ArrayLen => {
            debug_assert_eq!(args.len(), 1);
            let array = args[0];
            FunRet::Val(heap[array + heap::ARRAY_LEN_FIELD_IDX])
        }

        BuiltinFunDecl::ArrayGet { t } => {
            debug_assert_eq!(args.len(), 2);
            let array = args[0];
            let idx = val_as_u32(args[1]);
            FunRet::Val(heap.array_get(array, idx, Repr::from_mono_ty(t), loc, call_stack))
        }

        BuiltinFunDecl::ArraySet { t } => {
            debug_assert_eq!(args.len(), 3);
            let array = args[0];
            let idx = val_as_u32(args[1]);
            let elem = args[2];
            heap.array_set(array, idx, elem, Repr::from_mono_ty(t), loc, call_stack);
            FunRet::Val(pgm.unit_alloc)
        }

        BuiltinFunDecl::ArrayCopyWithin { t } => {
            debug_assert_eq!(args.len(), 4); // array, src, dst, len
            let array = args[0];
            let src = val_as_u32(args[1]);
            let dst = val_as_u32(args[2]);
            let len = val_as_u32(args[3]);
            heap.array_copy_within(array, src, dst, len, Repr::from_mono_ty(t), loc, call_stack);
            FunRet::Val(pgm.unit_alloc)
        }

        BuiltinFunDecl::ReadFileUtf8 => {
            debug_assert_eq!(args.len(), 1);
            let path = args[0];
            let path_str = std::str::from_utf8(heap.str_bytes(path)).unwrap();
            let file_contents = crate::read_file_utf8(path_str);
            FunRet::Val(heap.allocate_str(
                pgm.str_con_idx.as_u64(),
                Repr::U8,
                file_contents.as_bytes(),
            ))
        }

        BuiltinFunDecl::GetArgs => {
            debug_assert_eq!(args.len(), 0);
            let arg_array = heap.allocate_array(Repr::U64, pgm.cli_args.len() as u32);
            for (i, arg) in pgm.cli_args.iter().enumerate() {
                let arg_val = heap.allocate_str(pgm.str_con_idx.as_u64(), Repr::U8, arg.as_bytes());
                heap.array_set(arg_array, i as u32, arg_val, Repr::U64, loc, &[]);
            }
            FunRet::Val(arg_array)
        }
    }
}

fn write_call_stack<W: std::fmt::Write>(call_stack: &[Frame], out: &mut W) {
    for frame in call_stack.iter().rev() {
        write!(out, "{}: ", loc_display(&frame.call_site)).unwrap();
        match &frame.kind {
            FrameKind::Builtin(builtin_fun_decl) => {
                writeln!(out, "Builtin: {builtin_fun_decl:?}").unwrap()
            }
            FrameKind::Source(source_fun_name) => {
                writeln!(out, "{source_fun_name}").unwrap();
            }
            FrameKind::Closure(loc) => {
                writeln!(out, "Closure at {}", loc_display(loc)).unwrap();
            }
        }
    }
}

#[allow(unused)]
fn print_call_stack(call_stack: &[Frame]) {
    let mut out = String::new();
    write_call_stack(call_stack, &mut out);
    println!("{out}");
}
