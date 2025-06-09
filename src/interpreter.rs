#![allow(clippy::needless_range_loop, clippy::too_many_arguments)]

const INITIAL_HEAP_SIZE_WORDS: usize = (1024 * 1024 * 1024) / 8; // 1 GiB

mod heap;

use heap::Heap;

use crate::ast::{self, Id, Loc, L};
use crate::collections::Map;
use crate::lowering::*;
use crate::mono_ast as mono;
use crate::record_collector::RecordShape;
use crate::utils::loc_display;

use std::cmp::Ordering;
use std::io::Write;

use bytemuck::{cast_slice, cast_slice_mut};

// Just lowered program with some extra cached stuff for easy access.
struct Pgm {
    heap_objs: Vec<HeapObj>,
    funs: Vec<Fun>,
    closures: Vec<Closure>,

    // Some allocations and type tags for the built-ins.
    true_alloc: u64,
    false_alloc: u64,
    ordering_less_alloc: u64,
    ordering_equal_alloc: u64,
    ordering_greater_alloc: u64,
    unit_alloc: u64,
    char_con_idx: HeapObjIdx,
    str_con_idx: HeapObjIdx,
    array_u8_con_idx: HeapObjIdx,
    array_u32_con_idx: HeapObjIdx,
    array_u64_con_idx: HeapObjIdx,

    /// To allocate return value of `try`: `Result.Ok` tags, indexed by type arguments.
    result_ok_cons: Map<Vec<mono::Type>, HeapObjIdx>,

    /// To allocate return value of `try`: `Result.Err` tags, indexed by type arguments.
    result_err_cons: Map<Vec<mono::Type>, HeapObjIdx>,
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
    fn init(lowered_pgm: LoweredPgm, heap: &mut Heap) -> Pgm {
        let LoweredPgm {
            mut heap_objs,
            funs,
            closures,
            true_con_idx,
            false_con_idx,
            char_con_idx,
            ordering_less_con_idx,
            ordering_equal_con_idx,
            ordering_greater_con_idx,
            str_con_idx,
            array_u8_con_idx,
            array_u32_con_idx,
            array_u64_con_idx,
            result_err_cons,
            result_ok_cons,
            unit_con_idx,
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
        let ordering_less_alloc = heap_objs[ordering_less_con_idx.as_usize()]
            .as_source_con()
            .alloc;
        let ordering_equal_alloc = heap_objs[ordering_equal_con_idx.as_usize()]
            .as_source_con()
            .alloc;
        let ordering_greater_alloc = heap_objs[ordering_greater_con_idx.as_usize()]
            .as_source_con()
            .alloc;
        let unit_alloc = heap.allocate_tag(unit_con_idx.as_u64());

        Pgm {
            heap_objs,
            funs,
            closures,
            true_alloc,
            false_alloc,
            ordering_less_alloc,
            ordering_equal_alloc,
            ordering_greater_alloc,
            unit_alloc,
            char_con_idx,
            str_con_idx,
            array_u8_con_idx,
            array_u32_con_idx,
            array_u64_con_idx,
            result_err_cons,
            result_ok_cons,
        }
    }
}

/// Run the program, passing the arguments `args` as the `Array[Str]` argument to `main`.
pub fn run_with_args<W: Write>(w: &mut W, pgm: LoweredPgm, main: &str, args: &[String]) {
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

    // Check if main takes an input argument.
    let arg_vec: Vec<u64> = match main_fun.params.len() {
        0 => {
            if args.len() > 1 {
                println!(
                    "WARNING: Main function `{}` does not take command line arguments, but command line arguments are passed to the interpreter",
                    main
                );
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
            "Main function `{}` needs to take 0 or 1 argument, but it takes {} arguments",
            main, other
        ),
    };

    // Note: normally `call_fun` adjusts the stack, but when calling `main` we don't call
    // `call_fun`, so we add `main` here.
    let mut call_stack = vec![Frame {
        kind: FrameKind::Source(main_fun.name.node.clone()),
        call_site: Loc::dummy(),
    }];

    call_ast_fun(
        w,
        &pgm,
        &mut heap,
        main_fun,
        arg_vec,
        &call_loc,
        &mut call_stack,
    );
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
    assert_eq!(
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
    args: &[CallArg],
    loc: &Loc,
    call_stack: &mut Vec<Frame>,
) -> ControlFlow {
    match HeapObjIdx(heap[fun] as u32) {
        CONSTR_CON_IDX => {
            let con_idx = HeapObjIdx(heap[fun + 1] as u32);
            allocate_object_from_idx(w, pgm, heap, locals, con_idx, args, call_stack)
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
                    &arg.expr.loc,
                    call_stack
                )));
            }
            call_fun(w, pgm, heap, fun, arg_values, loc, call_stack).into_control_flow()
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
                    &arg.expr.loc,
                    call_stack
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
            assert_eq!(args.len(), closure.params.len());

            for (i, arg_val) in args.iter().enumerate() {
                let arg_val = val!(eval(
                    w,
                    pgm,
                    heap,
                    locals,
                    &arg_val.expr.node,
                    &arg_val.expr.loc,
                    call_stack
                ));
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
    args: &[CallArg],
    call_stack: &mut Vec<Frame>,
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
                    &arg.expr.loc,
                    call_stack
                )));
            }
        }

        ConFields::Named(field_names) => {
            // Evalaute in program order, store based on the order of the names
            // in the type.
            let mut named_values: Map<Id, u64> = Default::default();
            for arg in args {
                let name = arg.name.as_ref().unwrap().clone();
                let value = val!(eval(
                    w,
                    pgm,
                    heap,
                    locals,
                    &arg.expr.node,
                    &arg.expr.loc,
                    call_stack
                ));
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

            Stmt::Assign(AssignStmt { lhs, rhs, op }) => {
                // Complex assignment operators should've been desugared during type checking.
                debug_assert_eq!(
                    *op,
                    ast::AssignOp::Eq,
                    "{}: Complex assignment: {:?}",
                    loc_display(&stmt.loc),
                    op
                );
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

            Stmt::For(ForStmt {
                pat,
                expr,
                body,
                next_method,
                option_some_con,
            }) => {
                let iter = val!(eval(
                    w, pgm, heap, locals, &expr.node, &expr.loc, call_stack
                ));

                loop {
                    let next_item_option = match call_fun(
                        w,
                        pgm,
                        heap,
                        &pgm.funs[next_method.as_usize()],
                        vec![iter],
                        &expr.loc,
                        call_stack,
                    ) {
                        FunRet::Val(val) => val,
                        FunRet::Unwind(val) => return ControlFlow::Unwind(val),
                    };

                    if heap[next_item_option] != option_some_con.as_u64() {
                        break;
                    }

                    let value = heap[next_item_option + 1];

                    if !try_bind_pat(pgm, heap, pat, locals, value) {
                        panic!(
                            "{}: For loop pattern failed to match item",
                            loc_display(&pat.loc)
                        )
                    }

                    match exec(w, pgm, heap, locals, body, call_stack) {
                        ControlFlow::Val(_) => {}
                        ControlFlow::Ret(val) => {
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
                            return ControlFlow::Unwind(val);
                        }
                    }
                }

                0
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
    call_stack: &mut Vec<Frame>,
) -> ControlFlow {
    match expr {
        Expr::LocalVar(local_idx) => ControlFlow::Val(locals[local_idx.as_usize()]),

        Expr::TopVar(fun_idx) => ControlFlow::Val(heap.allocate_fun(fun_idx.as_u64())),

        Expr::Constr(con_idx) => {
            let con = pgm.heap_objs[con_idx.as_usize()].as_source_con();

            if con.fields.is_empty() {
                return ControlFlow::Val(con.alloc);
            }

            ControlFlow::Val(heap.allocate_constr(con_idx.as_u64()))
        }

        Expr::FieldSelect(FieldSelectExpr { object, field }) => {
            let object = val!(eval(
                w,
                pgm,
                heap,
                locals,
                &object.node,
                &object.loc,
                call_stack
            ));
            let object_tag = heap[object];
            let heap_obj = &pgm.heap_objs[object_tag as usize];
            let field_idx = match heap_obj {
                HeapObj::Source(source_con_decl) => {
                    let fields = &source_con_decl.fields;
                    fields.find_named_field_idx(field)
                }

                HeapObj::Record(record_shape) => match record_shape {
                    RecordShape::NamedFields { fields } => fields
                        .iter()
                        .enumerate()
                        .find_map(|(i, field_)| if field == field_ { Some(i) } else { None })
                        .unwrap(),
                    RecordShape::UnnamedFields { .. } => panic!(),
                },

                HeapObj::Builtin(builtin) => panic!(
                    "{}: Trying to select field of {:?}, object addr = {}",
                    loc_display(loc),
                    builtin,
                    object
                ),

                HeapObj::Variant(_) => panic!(),
            };

            ControlFlow::Val(heap[object + 1 + (field_idx as u64)])
        }

        Expr::MethodSelect(MethodSelectExpr { object, fun_idx }) => {
            let object = val!(eval(
                w,
                pgm,
                heap,
                locals,
                &object.node,
                &object.loc,
                call_stack
            ));
            ControlFlow::Val(heap.allocate_method(object, fun_idx.as_u64()))
        }

        Expr::AssocFnSelect(idx) => ControlFlow::Val(heap.allocate_fun(idx.as_u64())),

        Expr::Call(CallExpr { fun, args }) => {
            // See if `fun` is a method, associated function, or constructor to avoid closure
            // allocations.
            let fun: u64 = match &fun.node {
                Expr::Constr(con_idx) => {
                    return allocate_object_from_idx(
                        w, pgm, heap, locals, *con_idx, args, call_stack,
                    );
                }

                Expr::MethodSelect(MethodSelectExpr { object, fun_idx }) => {
                    let object = val!(eval(
                        w,
                        pgm,
                        heap,
                        locals,
                        &object.node,
                        &object.loc,
                        call_stack
                    ));
                    let mut arg_vals: Vec<u64> = Vec::with_capacity(args.len() + 1);
                    arg_vals.push(object);
                    for arg in args {
                        arg_vals.push(val!(eval(
                            w,
                            pgm,
                            heap,
                            locals,
                            &arg.expr.node,
                            &arg.expr.loc,
                            call_stack
                        )));
                    }
                    let fun = &pgm.funs[fun_idx.as_usize()];
                    return call_fun(w, pgm, heap, fun, arg_vals, loc, call_stack)
                        .into_control_flow();
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
                            &arg.expr.loc,
                            call_stack
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
                        let str = val!(eval(
                            w, pgm, heap, locals, &expr.node, &expr.loc, call_stack
                        ));
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
            let e = val!(eval(w, pgm, heap, locals, &e.node, &e.loc, call_stack));
            let val = if e == pgm.true_alloc {
                pgm.false_alloc
            } else {
                debug_assert_eq!(e, pgm.false_alloc);
                pgm.true_alloc
            };
            ControlFlow::Val(val)
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
            for Alt {
                pattern,
                guard,
                rhs,
            } in alts
            {
                if try_bind_pat(pgm, heap, pattern, locals, scrut) {
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
                        &field.node.loc,
                        call_stack
                    ));
                    let field_idx = *name_indices.get(field.name.as_ref().unwrap()).unwrap();
                    heap[record + 1 + (field_idx as u64)] = field_value;
                }
            } else {
                for (idx, ast::Named { name, node }) in fields.iter().enumerate() {
                    debug_assert!(name.is_none());
                    let value = val!(eval(
                        w, pgm, heap, locals, &node.node, &node.loc, call_stack
                    ));
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
                        &field.node.loc,
                        call_stack
                    ));
                    let field_idx = *name_indices.get(field.name.as_ref().unwrap()).unwrap();
                    heap[variant + 1 + (field_idx as u64)] = field_value;
                }
            } else {
                for (idx, ast::Named { name, node }) in fields.iter().enumerate() {
                    debug_assert!(name.is_none());
                    let value = val!(eval(
                        w, pgm, heap, locals, &node.node, &node.loc, call_stack
                    ));
                    heap[variant + (idx as u64) + 1] = value;
                }
            }

            ControlFlow::Val(variant)
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

        Expr::FieldSelect(FieldSelectExpr { object, field }) => {
            let object = val!(eval(
                w,
                pgm,
                heap,
                locals,
                &object.node,
                &object.loc,
                call_stack,
            ));
            let object_idx = heap[object];
            let object_con = pgm.heap_objs[object_idx as usize].as_source_con();
            let object_fields = &object_con.fields;
            let field_idx = object_fields.find_named_field_idx(field);
            heap[object + 1 + (field_idx as u64)] = val;
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
            value_bytes == str.as_bytes()
        }

        Pat::StrPfx(pfx, var) => {
            debug_assert!(heap[value] == pgm.str_con_idx.as_u64());
            let value_bytes = heap.str_bytes(value);
            if value_bytes.starts_with(pfx.as_bytes()) {
                if let Some(var) = var {
                    let pfx_len = pfx.len() as u32;
                    let len = heap.str_bytes(value).len() as u32;
                    let rest = heap.allocate_str_view(
                        pgm.str_con_idx.as_u64(),
                        value,
                        pfx_len,
                        len - pfx_len,
                    );
                    locals[var.as_usize()] = rest;
                }
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

            // Consturctor can have more fields than the pattern, so iterate pattern fields.
            for (mut field_idx, field_pat) in field_pats.iter().enumerate() {
                if let Some(field_name) = &field_pat.name {
                    field_idx = con.fields.find_named_field_idx(field_name);
                }
                let field_value = heap[value + 1 + (field_idx as u64)];
                if !try_bind_pat(pgm, heap, &field_pat.node, locals, field_value) {
                    return false;
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
                        let field_pat = match field_pats.iter().find_map(|pat| {
                            if pat.name.as_ref().unwrap() == field_name {
                                Some(&pat.node)
                            } else {
                                None
                            }
                        }) {
                            None => continue,
                            Some(pat) => pat,
                        };
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
            use std::fmt::Write;
            for frame in call_stack {
                write!(&mut msg_str, "{}: ", loc_display(&frame.call_site)).unwrap();
                match &frame.kind {
                    FrameKind::Builtin(builtin_fun_decl) => {
                        writeln!(&mut msg_str, "Builtin: {:?}", builtin_fun_decl).unwrap()
                    }
                    FrameKind::Source(source_fun_name) => {
                        msg_str.push_str(source_fun_name);
                        msg_str.push('\n');
                    }
                    FrameKind::Closure(loc) => {
                        writeln!(&mut msg_str, "Closure at {}", loc_display(loc)).unwrap();
                    }
                }
            }
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
                pgm.array_u8_con_idx.as_u64(),
                format!("{}", val_as_i8(i)).as_bytes(),
            ))
        }

        BuiltinFunDecl::ToStrU8 => {
            debug_assert_eq!(args.len(), 1);
            let i = args[0];
            FunRet::Val(heap.allocate_str(
                pgm.str_con_idx.as_u64(),
                pgm.array_u8_con_idx.as_u64(),
                format!("{}", val_as_u8(i)).as_bytes(),
            ))
        }

        BuiltinFunDecl::ToStrI32 => {
            debug_assert_eq!(args.len(), 1);
            let i = args[0];
            FunRet::Val(heap.allocate_str(
                pgm.str_con_idx.as_u64(),
                pgm.array_u8_con_idx.as_u64(),
                format!("{}", val_as_i32(i)).as_bytes(),
            ))
        }

        BuiltinFunDecl::ToStrU32 => {
            debug_assert_eq!(args.len(), 1);
            let i = args[0];
            FunRet::Val(heap.allocate_str(
                pgm.str_con_idx.as_u64(),
                pgm.array_u8_con_idx.as_u64(),
                format!("{}", val_as_u32(i)).as_bytes(),
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

        BuiltinFunDecl::Throw => {
            debug_assert_eq!(args.len(), 1);
            let exn = args[0];
            FunRet::Unwind(exn)
        }

        BuiltinFunDecl::Try { exn, a } => {
            debug_assert_eq!(args.len(), 1);
            let cb = args[0];

            // NB. No need to pass locals here as locals are used to evaluate closure arguments, and
            // we don't pass any arguments.
            let (val, con_idx) = match call_closure(w, pgm, heap, &mut [], cb, &[], loc, call_stack)
            {
                ControlFlow::Val(val) => (
                    val,
                    pgm.result_ok_cons
                        .get(&vec![exn.clone(), a.clone()])
                        .unwrap(),
                ),

                ControlFlow::Unwind(val) => (
                    val,
                    pgm.result_err_cons
                        .get(&vec![exn.clone(), a.clone()])
                        .unwrap(),
                ),

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
            let cap_words = (cap as usize) * repr.elem_size_in_bytes().div_ceil(8);
            let array = heap.allocate(cap_words + 2);
            heap[array] = (match repr {
                Repr::U8 => pgm.array_u8_con_idx,
                Repr::U32 => pgm.array_u32_con_idx,
                Repr::U64 => pgm.array_u64_con_idx,
            })
            .as_u64();
            heap[array + 1] = u32_as_val(cap);
            heap.values[(array + 2) as usize..(array as usize) + 2 + cap_words].fill(0);
            FunRet::Val(array)
        }

        BuiltinFunDecl::ArrayLen => {
            debug_assert_eq!(args.len(), 1);
            let array = args[0];
            FunRet::Val(heap[array + 1])
        }

        BuiltinFunDecl::ArrayGet { t } => {
            debug_assert_eq!(args.len(), 2);
            let array = args[0];
            let idx = val_as_u32(args[1]);
            let array_len = val_as_u32(heap[array + 1]);
            if idx >= array_len {
                panic!(
                    "{}: OOB array access (idx = {}, len = {})",
                    loc_display(loc),
                    idx,
                    array_len
                );
            }
            FunRet::Val(match Repr::from_mono_ty(t) {
                Repr::U8 => {
                    let payload: &[u8] = cast_slice(&heap.values[array as usize + 2..]);
                    u8_as_val(payload[idx as usize])
                }
                Repr::U32 => {
                    let payload: &[u32] = cast_slice(&heap.values[array as usize + 2..]);
                    u32_as_val(payload[idx as usize])
                }
                Repr::U64 => {
                    let payload: &[u64] = cast_slice(&heap.values[array as usize + 2..]);
                    payload[idx as usize]
                }
            })
        }

        BuiltinFunDecl::ArraySet { t } => {
            debug_assert_eq!(args.len(), 3);
            let array = args[0];
            let idx = args[1];
            let elem = args[2];

            let array_len = heap[array + 1];
            if idx >= array_len {
                panic!("OOB array access (idx = {}, len = {})", idx, array_len);
            }

            match Repr::from_mono_ty(t) {
                Repr::U8 => {
                    let payload: &mut [u8] = cast_slice_mut(&mut heap.values[array as usize + 2..]);
                    payload[idx as usize] = val_as_u8(elem);
                }

                Repr::U32 => {
                    let payload: &mut [u32] =
                        cast_slice_mut(&mut heap.values[array as usize + 2..]);
                    payload[idx as usize] = val_as_u32(elem);
                }

                Repr::U64 => {
                    let payload: &mut [u64] =
                        cast_slice_mut(&mut heap.values[array as usize + 2..]);
                    payload[idx as usize] = elem;
                }
            }

            FunRet::Val(pgm.unit_alloc)
        }

        BuiltinFunDecl::ReadFileUtf8 => {
            debug_assert_eq!(args.len(), 1);
            let path = args[0];
            let path_str = std::str::from_utf8(heap.str_bytes(path)).unwrap();
            let file_contents = crate::read_file_utf8(path_str);
            FunRet::Val(heap.allocate_str(
                pgm.str_con_idx.as_u64(),
                pgm.array_u8_con_idx.as_u64(),
                file_contents.as_bytes(),
            ))
        }
    }
}
