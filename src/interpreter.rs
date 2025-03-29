#![allow(clippy::needless_range_loop, clippy::too_many_arguments)]

const INITIAL_HEAP_SIZE_WORDS: usize = (1024 * 1024 * 1024) / 8; // 1 GiB

mod heap;

use heap::Heap;

use crate::ast::{self, Id, Loc, L};
use crate::collections::Map;
use crate::lowering::*;
use crate::record_collector::RecordShape;
use crate::utils::loc_display;

use std::io::Write;

use bytemuck::cast_slice_mut;

// Just lowered program with some extra cached stuff for easy access.
struct Pgm {
    heap_objs: Vec<HeapObj>,
    funs: Vec<Fun>,
    closures: Vec<Closure>,

    // Some allocations and type tags for the built-ins.
    true_alloc: u64,
    false_alloc: u64,
    char_con_idx: HeapObjIdx,
    str_con_idx: HeapObjIdx,
    i8_con_idx: HeapObjIdx,
    u8_con_idx: HeapObjIdx,
    i32_con_idx: HeapObjIdx,
    u32_con_idx: HeapObjIdx,
    array_i8_con_idx: HeapObjIdx,
    array_u8_con_idx: HeapObjIdx,
    array_i32_con_idx: HeapObjIdx,
    array_u32_con_idx: HeapObjIdx,
    array_i64_con_idx: HeapObjIdx,
    array_u64_con_idx: HeapObjIdx,
}

impl Pgm {
    fn init(lowered_pgm: LoweredPgm, heap: &mut Heap) -> Pgm {
        let LoweredPgm {
            mut heap_objs,
            funs,
            closures,
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
        for heap_obj in heap_objs.iter_mut() {
            let source_con = match heap_obj {
                HeapObj::Builtin(_) | HeapObj::Record(_) | HeapObj::Variant(_) => continue,
                HeapObj::Source(source_con) => source_con,
            };

            if !source_con.fields.is_empty() {
                continue;
            }

            source_con.alloc = heap.allocate_tag(source_con.idx.as_u64());
        }

        let true_alloc = heap_objs[true_con_idx.as_usize()].as_source_con().alloc;
        let false_alloc = heap_objs[false_con_idx.as_usize()].as_source_con().alloc;

        Pgm {
            heap_objs,
            funs,
            closures,
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

    call_ast_fun(w, &pgm, &mut heap, main_fun, arg_vec, &call_loc);
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
) -> FunRet {
    match fun {
        Fun::Builtin(builtin) => call_builtin_fun(w, pgm, heap, builtin, args, loc),
        Fun::Source(source) => call_ast_fun(w, pgm, heap, source, args, loc),
    }
}

fn call_builtin_fun<W: Write>(
    _w: &mut W,
    _pgm: &Pgm,
    _heap: &mut Heap,
    _fun: &BuiltinFunDecl,
    _args: Vec<u64>,
    _loc: &Loc,
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

fn call_closure<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    locals: &mut [u64],
    fun: u64,
    args: &[CallArg],
    loc: &Loc,
) -> ControlFlow {
    match HeapObjIdx(heap[fun] as u32) {
        CONSTR_CON_IDX => {
            let con_idx = HeapObjIdx(heap[fun + 1] as u32);
            allocate_object_from_idx(w, pgm, heap, locals, con_idx, args)
        }

        FUN_CON_IDX => {
            let top_fun_idx = heap[fun + 1];
            let fun = &pgm.funs[top_fun_idx as usize];
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
            call_fun(w, pgm, heap, fun, arg_values, loc).into_control_flow()
        }

        METHOD_CON_IDX => {
            let receiver = heap[fun + 1];
            let fun_idx = heap[fun + 2];
            let fun = &pgm.funs[fun_idx as usize];
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

        CLOSURE_CON_IDX => {
            let closure_idx = heap[fun + 1];
            let closure = &pgm.closures[closure_idx as usize];

            let mut closure_locals: Vec<u64> = vec![0; closure.locals.len()];

            // Load closure's free variables into locals.
            for (i, fv) in closure.fvs.iter().enumerate() {
                let fv_value = heap[fun + 1 + (i as u64)];
                closure_locals[fv.use_idx.as_usize()] = fv_value;
            }

            // Copy closure arguments into locals.
            assert_eq!(args.len(), closure.params.len());

            for (i, arg_val) in args.iter().enumerate() {
                let arg_val = val!(eval(
                    w,
                    pgm,
                    heap,
                    locals,
                    &arg_val.expr.node,
                    &arg_val.expr.loc
                ));
                locals[i] = arg_val;
            }

            match exec(w, pgm, heap, &mut closure_locals, &closure.body) {
                ControlFlow::Val(val) | ControlFlow::Ret(val) => ControlFlow::Val(val),
                ControlFlow::Break(_) | ControlFlow::Continue(_) => panic!(),
                ControlFlow::Unwind(val) => ControlFlow::Unwind(val),
            }
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
    args: &[CallArg],
) -> ControlFlow {
    let con = pgm.heap_objs[con_idx.as_usize()].as_source_con();
    let fields = &con.fields;
    let mut arg_values: Vec<u64> = Vec::with_capacity(args.len());

    match fields {
        ConFields::Unnamed(num_fields) => {
            // Evaluate in program order and store in the same order.
            assert_eq!(num_fields.len(), args.len());
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

        ConFields::Named(field_names) => {
            // Evalaute in program order, store based on the order of the names
            // in the type.
            let mut named_values: Map<Id, u64> = Default::default();
            for arg in args {
                let name = arg.name.as_ref().unwrap().clone();
                let value = val!(eval(w, pgm, heap, locals, &arg.expr.node, &arg.expr.loc));
                let old = named_values.insert(name.clone(), value);
                assert!(old.is_none());
            }
            for (name, _) in field_names {
                arg_values.push(*named_values.get(name).unwrap());
            }
        }
    }

    let object = heap.allocate(1 + args.len());
    heap[object] = con_idx.as_u64();
    for (arg_idx, arg_value) in arg_values.into_iter().enumerate() {
        heap[object + 1 + (arg_idx as u64)] = arg_value;
    }

    ControlFlow::Val(object)
}

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
                pat: _,
                expr: _,
                body: _,
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
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    locals: &mut [u64],
    expr: &Expr,
    loc: &Loc,
) -> ControlFlow {
    match expr {
        Expr::LocalVar(local_idx) => ControlFlow::Val(locals[local_idx.as_usize()]),

        Expr::TopVar(fun_idx) => ControlFlow::Val(heap.allocate_fun(fun_idx.as_u64())),

        Expr::Constr(con_idx) => {
            let con = pgm.heap_objs[con_idx.as_usize()].as_source_con();

            if con.fields.is_empty() {
                return ControlFlow::Val(con.alloc);
            }

            return ControlFlow::Val(heap.allocate_constr(con_idx.as_u64()));
        }

        Expr::FieldSelect(FieldSelectExpr { object, field }) => {
            let object = val!(eval(w, pgm, heap, locals, &object.node, &object.loc));
            let object_tag = heap[object];
            let con = &pgm.heap_objs[object_tag as usize];
            let fields = &con.as_source_con().fields;
            let field_idx = fields.find_named_field_idx(field);
            ControlFlow::Val(heap[object + 1 + (field_idx as u64)])
        }

        Expr::MethodSelect(MethodSelectExpr { object, fun_idx }) => {
            let object = val!(eval(w, pgm, heap, locals, &object.node, &object.loc));
            ControlFlow::Val(heap.allocate_method(object, fun_idx.as_u64()))
        }

        Expr::AssocFnSelect(idx) => ControlFlow::Val(heap.allocate_fun(idx.as_u64())),

        Expr::Call(CallExpr { fun, args }) => {
            // See if `fun` is a method, associated function, or constructor to avoid closure
            // allocations.
            let fun: u64 = match &fun.node {
                Expr::Constr(con_idx) => {
                    return allocate_object_from_idx(w, pgm, heap, locals, *con_idx, args);
                }

                Expr::MethodSelect(MethodSelectExpr { object, fun_idx }) => {
                    let object = val!(eval(w, pgm, heap, locals, &object.node, &object.loc));
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
                    let fun = &pgm.funs[fun_idx.as_usize()];
                    return call_fun(w, pgm, heap, fun, arg_vals, loc).into_control_flow();
                }

                Expr::AssocFnSelect(fun_idx) => {
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
                    let fun = &pgm.funs[fun_idx.as_usize()];
                    return call_fun(w, pgm, heap, fun, arg_vals, loc).into_control_flow();
                }

                _ => val!(eval(w, pgm, heap, locals, &fun.node, &fun.loc)),
            };

            // Slow path calls a closure.
            call_closure(w, pgm, heap, locals, fun, args, loc)
        }

        Expr::Int(ast::IntExpr { parsed, .. }) => ControlFlow::Val(*parsed),

        Expr::Char(char) => {
            let alloc = heap.allocate(2);
            heap[alloc] = pgm.char_con_idx.as_u64();
            heap[alloc + 1] = u32_as_val(*char as u32);
            ControlFlow::Val(alloc)
        }

        Expr::String(parts) => {
            let mut bytes: Vec<u8> = vec![];
            for part in parts {
                match part {
                    StringPart::Str(str) => bytes.extend(str.as_bytes()),
                    StringPart::Expr(expr) => {
                        let str = val!(eval(w, pgm, heap, locals, &expr.node, &expr.loc));
                        debug_assert_eq!(heap[str], pgm.str_con_idx.as_u64());
                        let part_bytes = heap.str_bytes(str);
                        bytes.extend(part_bytes);
                    }
                }
            }
            ControlFlow::Val(heap.allocate_str(
                pgm.str_con_idx.as_u64(),
                pgm.array_u8_con_idx.as_u64(),
                &bytes,
            ))
        }

        Expr::BoolNot(e) => {
            let e = val!(eval(w, pgm, heap, locals, &e.node, &e.loc));
            let val = if e == pgm.true_alloc {
                pgm.false_alloc
            } else {
                debug_assert_eq!(e, pgm.false_alloc);
                pgm.true_alloc
            };
            ControlFlow::Val(val)
        }

        Expr::BoolAnd(left, right) => {
            let left = val!(eval(w, pgm, heap, locals, &left.node, &left.loc));
            if left == pgm.false_alloc {
                ControlFlow::Val(pgm.false_alloc)
            } else {
                eval(w, pgm, heap, locals, &right.node, &right.loc)
            }
        }

        Expr::BoolOr(left, right) => {
            let left = val!(eval(w, pgm, heap, locals, &left.node, &left.loc));
            if left == pgm.true_alloc {
                ControlFlow::Val(pgm.true_alloc)
            } else {
                eval(w, pgm, heap, locals, &right.node, &right.loc)
            }
        }

        Expr::Return(expr) => {
            ControlFlow::Ret(val!(eval(w, pgm, heap, locals, &expr.node, &expr.loc)))
        }

        Expr::Match(MatchExpr { scrutinee, alts }) => {
            let scrut = val!(eval(w, pgm, heap, locals, &scrutinee.node, &scrutinee.loc));
            for Alt {
                pattern,
                guard,
                rhs,
            } in alts
            {
                assert!(guard.is_none()); // TODO
                if try_bind_pat(pgm, heap, pattern, locals, scrut) {
                    return exec(w, pgm, heap, locals, rhs);
                }
            }
            panic!("{}: Non-exhaustive pattern match", loc_display(loc));
        }

        Expr::If(IfExpr {
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

        Expr::Record(RecordExpr { fields, idx }) => {
            let shape = pgm.heap_objs[idx.as_usize()].as_record();

            let record = heap.allocate(fields.len() + 1);
            heap[record] = idx.as_u64();

            if !fields.is_empty() && fields[0].name.is_some() {
                let name_indices: Map<Id, usize> = match shape {
                    RecordShape::UnnamedFields { .. } => panic!(),
                    RecordShape::NamedFields { fields } => fields
                        .iter()
                        .enumerate()
                        .map(|(i, name)| (name.clone(), i))
                        .collect(),
                };

                for field in fields {
                    let field_value = val!(eval(
                        w,
                        pgm,
                        heap,
                        locals,
                        &field.node.node,
                        &field.node.loc
                    ));
                    let field_idx = *name_indices.get(field.name.as_ref().unwrap()).unwrap();
                    heap[record + 1 + (field_idx as u64)] = field_value;
                }
            } else {
                for (idx, ast::Named { name, node }) in fields.iter().enumerate() {
                    debug_assert!(name.is_none());
                    let value = val!(eval(w, pgm, heap, locals, &node.node, &node.loc));
                    heap[record + (idx as u64) + 1] = value;
                }
            }

            ControlFlow::Val(record)
        }

        Expr::Variant(VariantExpr { id: _, fields, idx }) => {
            let shape = pgm.heap_objs[idx.as_usize()].as_variant();

            let variant = heap.allocate(fields.len() + 1);
            heap[variant] = idx.as_u64();

            if !fields.is_empty() && fields[0].name.is_some() {
                let name_indices: Map<Id, usize> = match &shape.payload {
                    RecordShape::UnnamedFields { .. } => panic!(),
                    RecordShape::NamedFields { fields } => fields
                        .iter()
                        .enumerate()
                        .map(|(i, name)| (name.clone(), i))
                        .collect(),
                };

                for field in fields {
                    let field_value = val!(eval(
                        w,
                        pgm,
                        heap,
                        locals,
                        &field.node.node,
                        &field.node.loc
                    ));
                    let field_idx = *name_indices.get(field.name.as_ref().unwrap()).unwrap();
                    heap[variant + 1 + (field_idx as u64)] = field_value;
                }
            } else {
                for (idx, ast::Named { name, node }) in fields.iter().enumerate() {
                    debug_assert!(name.is_none());
                    let value = val!(eval(w, pgm, heap, locals, &node.node, &node.loc));
                    heap[variant + (idx as u64) + 1] = value;
                }
            }

            ControlFlow::Val(variant)
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
) -> ControlFlow {
    match &lhs.node {
        Expr::LocalVar(local_idx) => {
            locals[local_idx.as_usize()] = val;
        }

        Expr::FieldSelect(FieldSelectExpr { object, field }) => {
            let object = val!(eval(w, pgm, heap, locals, &object.node, &object.loc));
            let object_idx = heap[object];
            let object_con = pgm.heap_objs[object_idx as usize].as_source_con();
            let object_fields = &object_con.fields;
            let field_idx = object_fields.find_named_field_idx(field);
            heap[object + 1 + (field_idx as u64)] = val;
        }

        _ => todo!("Assign statement with fancy LHS at {:?}", &lhs.loc),
    }
    ControlFlow::Val(val)
}

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
    match &pattern.node {
        Pat::Var(var) => {
            locals[var.as_usize()] = value;
            true
        }

        Pat::Ignore => true,

        Pat::Str(str) => {
            debug_assert!(heap[value] == pgm.str_con_idx.as_u64());
            let value_bytes = heap.str_bytes(value);
            if value_bytes == str.as_bytes() {
                true
            } else {
                false
            }
        }

        Pat::StrPfx(pfx, var) => {
            debug_assert!(heap[value] == pgm.str_con_idx.as_u64());
            let value_bytes = heap.str_bytes(value);
            if value_bytes.starts_with(pfx.as_bytes()) {
                let pfx_len = pfx.len() as u32;
                let len = heap.str_bytes(value).len() as u32;
                let rest =
                    heap.allocate_str_view(pgm.str_con_idx.as_u64(), value, pfx_len, len - pfx_len);
                locals[var.as_usize()] = rest;
                true
            } else {
                false
            }
        }

        Pat::Char(char) => {
            debug_assert_eq!(heap[value], pgm.char_con_idx.as_u64());
            heap[value + 1] == u64::from(*char as u32)
        }

        Pat::Or(pat1, pat2) => {
            try_bind_pat(pgm, heap, pat1, locals, value)
                || try_bind_pat(pgm, heap, pat2, locals, value)
        }

        Pat::Constr(ConstrPattern {
            constr: con_idx,
            fields: field_pats,
        }) => {
            let value_tag = heap[value];
            if value_tag != con_idx.as_u64() {
                return false;
            }

            let con = pgm.heap_objs[con_idx.as_usize()].as_source_con();
            match &con.fields {
                ConFields::Named(con_fields) => {
                    debug_assert!(field_pats.iter().all(|pat| pat.name.is_some()));
                    debug_assert_eq!(con_fields.len(), field_pats.len());
                    for (i, (con_field_name, _)) in con_fields.iter().enumerate() {
                        let field_value = heap[value + (i as u64)];
                        let field_pat = field_pats
                            .iter()
                            .find_map(|pat| {
                                if pat.name.as_ref().unwrap() == con_field_name {
                                    Some(&pat.node)
                                } else {
                                    None
                                }
                            })
                            .unwrap();
                        if !try_bind_pat(pgm, heap, field_pat, locals, field_value) {
                            return false;
                        }
                    }
                }

                ConFields::Unnamed(con_fields) => {
                    debug_assert!(field_pats.iter().all(|pat| pat.name.is_none()));
                    debug_assert_eq!(con_fields.len(), field_pats.len());
                    for (i, field_pat) in field_pats.iter().enumerate() {
                        let field_value = heap[value + (i as u64)];
                        if !try_bind_pat(pgm, heap, &field_pat.node, locals, field_value) {
                            return false;
                        }
                    }
                }
            }

            true
        }

        Pat::Record(RecordPattern {
            fields: field_pats,
            idx,
        }) => {
            let value_tag = heap[value];
            debug_assert_eq!(value_tag, idx.as_u64());

            let record_shape = pgm.heap_objs[idx.as_usize()].as_record();

            match record_shape {
                RecordShape::NamedFields { fields } => {
                    for (i, field_name) in fields.iter().enumerate() {
                        let field_pat = field_pats
                            .iter()
                            .find_map(|pat| {
                                if pat.name.as_ref().unwrap() == field_name {
                                    Some(&pat.node)
                                } else {
                                    None
                                }
                            })
                            .unwrap();
                        let field_value = heap[value + 1 + (i as u64)];
                        if !try_bind_pat(pgm, heap, field_pat, locals, field_value) {
                            return false;
                        }
                    }
                }

                RecordShape::UnnamedFields { arity } => {
                    debug_assert_eq!(*arity as usize, field_pats.len());
                    for (i, field_pat) in field_pats.iter().enumerate() {
                        debug_assert!(field_pat.name.is_none());
                        let field_value = heap[value + 1 + (i as u64)];
                        if !try_bind_pat(pgm, heap, &field_pat.node, locals, field_value) {
                            return false;
                        }
                    }
                }
            }

            true
        }

        Pat::Variant(VariantPattern {
            constr: _,
            fields: field_pats,
            idx,
        }) => {
            let value_tag = heap[value];

            if value_tag != idx.as_u64() {
                return false;
            }

            let variant_shape = pgm.heap_objs[idx.as_usize()].as_variant();
            let record_shape = &variant_shape.payload;

            match record_shape {
                RecordShape::NamedFields { fields } => {
                    for (i, field_name) in fields.iter().enumerate() {
                        let field_pat = field_pats
                            .iter()
                            .find_map(|pat| {
                                if pat.name.as_ref().unwrap() == field_name {
                                    Some(&pat.node)
                                } else {
                                    None
                                }
                            })
                            .unwrap();
                        let field_value = heap[value + 1 + (i as u64)];
                        if !try_bind_pat(pgm, heap, field_pat, locals, field_value) {
                            return false;
                        }
                    }
                }

                RecordShape::UnnamedFields { arity } => {
                    debug_assert_eq!(*arity as usize, field_pats.len());
                    for (i, field_pat) in field_pats.iter().enumerate() {
                        debug_assert!(field_pat.name.is_none());
                        let field_value = heap[value + 1 + (i as u64)];
                        if !try_bind_pat(pgm, heap, &field_pat.node, locals, field_value) {
                            return false;
                        }
                    }
                }
            }

            true
        }
    }
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
