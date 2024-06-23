//! An AST interpreter, feature complete enough to interpret the bootstrapping compiler.
//!
//! Since we don't have a proper type checker (it will be implemented in the bootstrapped compiler)
//! we don't assume type safety here and always check types.

#![allow(clippy::needless_range_loop, clippy::too_many_arguments)]

mod builtins;
mod heap;
mod init;

use builtins::{call_builtin_fun, BuiltinFun};
use heap::Heap;

use crate::ast::{self, L};
use crate::collections::{Map, Set};
use crate::interpolation::StringPart;
use crate::record_collector::{collect_records, RecordShape};

use std::cmp::Ordering;
use std::io::Write;

use bytemuck::cast_slice_mut;
use lexgen_util::Loc;
use smol_str::SmolStr;

pub fn run<W: Write>(w: &mut W, pgm: Vec<L<ast::TopDecl>>, input: &str) {
    let mut heap = Heap::new();
    let pgm = Pgm::new(pgm, &mut heap);

    // Allocate command line arguments to be passed to the program.
    let input = heap.allocate_str(input.as_bytes());

    // Find the main function.
    let main_fun = pgm.top_level_funs.get("main").unwrap();
    call(w, &pgm, &mut heap, main_fun, vec![input], Loc::default());
}

macro_rules! generate_ty_tags {
    ($($name:ident),* $(,)?) => {
        generate_ty_tags!(@generate 0, $($name),*);
    };

    (@generate $index:expr, $name:ident $(, $rest:ident)*) => {
        const $name: u64 = $index;
        generate_ty_tags!(@generate $index + 1, $($rest),*);
    };

    (@generate $index:expr,) => {};
}

#[rustfmt::skip]
generate_ty_tags!(
    FALSE_TYPE_TAG,
    TRUE_TYPE_TAG,
    I32_TYPE_TAG,
    STR_TYPE_TAG,
    STR_VIEW_TYPE_TAG,
    ARRAY_TYPE_TAG,
    CONSTR_TYPE_TAG,    // Constructor closure, e.g. `Option.Some`.
    TOP_FUN_TYPE_TAG,   // Top-level function closure, e.g. `id`.
    ASSOC_FUN_TYPE_TAG, // Associated function closure, e.g. `Value.toString`.
    FIRST_TYPE_TAG,     // First available type tag for user types.
);

#[derive(Debug, Default)]
struct Pgm {
    /// Type constructors by type name.
    ///
    /// These don't include records.
    ///
    /// This can be used when allocating.
    ty_cons: Map<SmolStr, TyCon>,

    /// Maps object tags to constructor info.
    cons_by_tag: Vec<Con>,

    /// Type tags of records.
    ///
    /// This can be used to get the tag of a record, from a record pattern, value, or type.
    record_ty_tags: Map<RecordShape, u64>,

    /// Associated functions, indexed by type tag, then function name.
    associated_funs: Vec<Map<SmolStr, Fun>>,

    /// Top-level functions, indexed by function name.
    top_level_funs: Map<SmolStr, Fun>,

    /// Same as `top_level_funs`, but indexed by the function index.
    top_level_funs_by_idx: Vec<Fun>,
}

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
        ty_name: SmolStr,
        con_name: Option<SmolStr>,
    },
    Record {
        #[allow(unused)]
        shape: RecordShape,
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
    name: Option<SmolStr>,

    /// Fields of the constructor, with names.
    ///
    /// Either all of the fields or none of them should be named.
    fields: Fields,
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

#[derive(Debug, Clone)]
enum Fields {
    Unnamed(u32),

    // NB. The vec shouldn't be empty. For nullary constructors use `Unnamed(0)`.
    Named(Vec<SmolStr>),
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

const INITIAL_HEAP_SIZE_WORDS: usize = (1024 * 1024 * 1024) / 8; // 1 GiB

#[derive(Debug)]
enum ControlFlow {
    /// Continue with the next statement.
    Next(u64),

    /// Return value from the function.
    Return(u64),
}

impl Pgm {
    fn new(pgm: Vec<L<ast::TopDecl>>, heap: &mut Heap) -> Pgm {
        // Initialize `ty_cons`.
        let (ty_cons, mut next_type_tag): (Map<SmolStr, TyCon>, u64) = init::collect_types(&pgm);

        fn convert_record(shape: &RecordShape) -> Fields {
            match shape {
                RecordShape::UnnamedFields { arity } => Fields::Unnamed(*arity),
                RecordShape::NamedFields { fields } => Fields::Named(fields.clone()),
            }
        }

        let mut cons_by_tag: Vec<Con> = vec![];

        let mut ty_cons_sorted: Vec<(SmolStr, TyCon)> = ty_cons
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        ty_cons_sorted.sort_by_key(|(_, ty_con)| ty_con.type_tag);

        for (ty_name, ty_con) in ty_cons_sorted {
            if ty_con.value_constrs.is_empty() {
                // A built-in type with no constructors.
                cons_by_tag.push(Con {
                    info: ConInfo::Named {
                        ty_name,
                        con_name: None,
                    },
                    fields: Fields::Unnamed(0),
                    alloc: None,
                });
            } else {
                for constr in ty_con.value_constrs {
                    let alloc: Option<u64> = if constr.fields.is_empty() {
                        Some(heap.allocate_tag(cons_by_tag.len() as u64))
                    } else {
                        None
                    };
                    cons_by_tag.push(Con {
                        info: ConInfo::Named {
                            ty_name: ty_name.clone(),
                            con_name: constr.name.clone(),
                        },
                        fields: constr.fields.clone(),
                        alloc,
                    });
                }
            }
        }

        // Initialize `record_ty_tags`.
        let record_shapes: Set<RecordShape> = collect_records(&pgm);
        let mut record_ty_tags: Map<RecordShape, u64> = Default::default();

        for record_shape in record_shapes {
            let fields = convert_record(&record_shape);
            cons_by_tag.push(Con {
                info: ConInfo::Record {
                    shape: record_shape.clone(),
                },
                fields,
                alloc: None,
            });
            record_ty_tags.insert(record_shape, next_type_tag);
            next_type_tag += 1;
        }

        // Initialize `associated_funs` and `top_level_funs`.
        let (top_level_funs, associated_funs) = init::collect_funs(pgm);

        let mut associated_funs_vec: Vec<Map<SmolStr, Fun>> =
            vec![Default::default(); next_type_tag as usize];

        for (ty_name, funs) in associated_funs {
            let ty_con = ty_cons.get(&ty_name).unwrap();
            let first_tag = ty_cons.get(&ty_name).unwrap().type_tag as usize;
            let n_constrs = ty_con.value_constrs.len();
            if n_constrs == 0 {
                // A built-in type with no constructor.
                associated_funs_vec[first_tag] = funs;
            } else {
                for tag in first_tag..first_tag + n_constrs {
                    associated_funs_vec[tag].clone_from(&funs);
                }
            }
        }

        // Initialize `top_level_funs_by_idx`.
        let mut top_level_funs_vec: Vec<(SmolStr, Fun)> = top_level_funs
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();

        top_level_funs_vec.sort_by_key(|(_, fun)| fun.idx);

        let top_level_funs_by_idx = top_level_funs_vec.into_iter().map(|(_, f)| f).collect();

        Pgm {
            ty_cons,
            cons_by_tag,
            record_ty_tags,
            associated_funs: associated_funs_vec,
            top_level_funs,
            top_level_funs_by_idx,
        }
    }

    fn get_tag_fields(&self, tag: u64) -> &Fields {
        &self.cons_by_tag[tag as usize].fields
    }

    fn true_alloc(&self) -> u64 {
        self.cons_by_tag[TRUE_TYPE_TAG as usize].alloc.unwrap()
    }

    fn false_alloc(&self) -> u64 {
        self.cons_by_tag[FALSE_TYPE_TAG as usize].alloc.unwrap()
    }

    fn bool_alloc(&self, b: bool) -> u64 {
        if b {
            self.true_alloc()
        } else {
            self.false_alloc()
        }
    }
}

fn call<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    fun: &Fun,
    args: Vec<u64>,
    loc: Loc,
) -> u64 {
    match &fun.kind {
        FunKind::Builtin(builtin) => call_builtin_fun(w, pgm, heap, builtin, args, loc),
        FunKind::Source(source) => call_source_fun(w, pgm, heap, source, args, loc),
    }
}

fn call_method<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    receiver: u64,
    method: &SmolStr,
    mut args: Vec<u64>,
    loc: Loc,
) -> u64 {
    let tag = heap[receiver];
    let fun = pgm.associated_funs[tag as usize]
        .get(method)
        .unwrap_or_else(|| panic!("Receiver with tag {} does not have {} method", tag, method));
    args.insert(0, receiver);
    call(w, pgm, heap, fun, args, loc)
}

fn call_source_fun<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    fun: &ast::FunDecl,
    args: Vec<u64>,
    loc: Loc,
) -> u64 {
    assert_eq!(
        fun.num_params(),
        args.len() as u32,
        "{}, fun: {}",
        LocDisplay(loc),
        fun.name
    );

    let mut locals: Map<SmolStr, u64> = Default::default();

    let mut arg_idx: usize = 0;
    if fun.self_ {
        locals.insert(SmolStr::new("self"), args[0]);
        arg_idx += 1;
    }

    for (param_name, _param_type) in &fun.params {
        let old = locals.insert(param_name.clone(), args[arg_idx]);
        assert!(old.is_none());
        arg_idx += 1;
    }

    match exec(w, pgm, heap, &mut locals, &fun.body.thing) {
        ControlFlow::Next(val) | ControlFlow::Return(val) => val,
    }
}

/// Allocate an object from type name and optional constructor name.
fn allocate_object_from_names<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    locals: &mut Map<SmolStr, u64>,
    ty: &SmolStr,
    constr_name: Option<SmolStr>,
    args: &[ast::CallArg],
    loc: Loc,
) -> u64 {
    let ty_con = pgm
        .ty_cons
        .get(ty)
        .unwrap_or_else(|| panic!("Undefined type {} at {}", ty, LocDisplay(loc)));

    let constr_idx = match constr_name {
        Some(constr_name) => {
            let (constr_idx_, _) = ty_con
                .value_constrs
                .iter()
                .enumerate()
                .find(|(_, constr)| constr.name.as_ref() == Some(&constr_name))
                .unwrap_or_else(|| {
                    panic!(
                        "Type {} does not have a constructor named {}",
                        ty, constr_name
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
    locals: &mut Map<SmolStr, u64>,
    constr_tag: u64,
    args: &[ast::CallArg],
) -> u64 {
    let fields = pgm.get_tag_fields(constr_tag);
    let mut arg_values = Vec::with_capacity(args.len());

    match fields {
        Fields::Unnamed(num_fields) => {
            // Evaluate in program order and store in the same order.
            assert_eq!(*num_fields as usize, args.len());
            for arg in args {
                assert!(arg.name.is_none());
                arg_values.push(eval(w, pgm, heap, locals, &arg.expr));
            }
        }

        Fields::Named(field_names) => {
            // Evalaute in program order, store based on the order of the names
            // in the type.
            let mut named_values: Map<SmolStr, u64> = Default::default();
            for arg in args {
                let name = arg.name.as_ref().unwrap().clone();
                let value = eval(w, pgm, heap, locals, &arg.expr);
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

    object
}

fn exec<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    locals: &mut Map<SmolStr, u64>,
    stmts: &[L<ast::Stmt>],
) -> ControlFlow {
    let mut return_value: u64 = 0;

    'next_stmt: for stmt in stmts {
        return_value = match &stmt.thing {
            ast::Stmt::Let(ast::LetStatement { lhs, ty: _, rhs }) => {
                let val = eval(w, pgm, heap, locals, rhs);
                // assert!(self.test_pattern(heap, locals, lhs, val));
                // self.bind_pattern(heap, locals, lhs, val);
                locals.insert(lhs.clone(), val);
                val
            }

            ast::Stmt::Match(ast::MatchStatement { scrutinee, alts }) => {
                let scrut = eval(w, pgm, heap, locals, scrutinee);
                for ast::Alt {
                    pattern,
                    guard,
                    rhs,
                } in alts
                {
                    assert!(guard.is_none()); // TODO
                    if test_pattern(pgm, heap, locals, pattern, scrut) {
                        bind_pattern(pgm, heap, locals, pattern, scrut);
                        match exec(w, pgm, heap, locals, rhs) {
                            ControlFlow::Next(val) => {
                                return_value = val;
                                continue 'next_stmt;
                            }
                            ControlFlow::Return(val) => return ControlFlow::Return(val),
                        }
                    }
                }
                panic!("Non-exhaustive pattern match");
            }

            ast::Stmt::If(ast::IfStatement {
                branches,
                else_branch,
            }) => {
                for (cond, stmts) in branches {
                    let cond = eval(w, pgm, heap, locals, cond);
                    assert!(heap[cond] <= TRUE_TYPE_TAG);
                    if heap[cond] == TRUE_TYPE_TAG {
                        match exec(w, pgm, heap, locals, stmts) {
                            ControlFlow::Next(val) => return_value = val,
                            ControlFlow::Return(val) => return ControlFlow::Return(val),
                        }
                        continue 'next_stmt;
                    }
                }
                if let Some(else_branch) = else_branch {
                    match exec(w, pgm, heap, locals, else_branch) {
                        ControlFlow::Next(val) => return_value = val,
                        ControlFlow::Return(val) => return ControlFlow::Return(val),
                    }
                }
                return_value
            }

            ast::Stmt::Assign(ast::AssignStatement { lhs, rhs, op }) => {
                let rhs = eval(w, pgm, heap, locals, rhs);
                assign(w, pgm, heap, locals, lhs, rhs, *op, stmt.start);
                rhs
            }

            ast::Stmt::Expr(expr) => eval(w, pgm, heap, locals, expr),

            ast::Stmt::While(ast::WhileStatement { cond, body }) => loop {
                let cond = eval(w, pgm, heap, locals, cond);
                if heap[cond] == FALSE_TYPE_TAG {
                    break 0; // FIXME: Return unit
                }
                match exec(w, pgm, heap, locals, body) {
                    ControlFlow::Next(_val) => {}
                    ControlFlow::Return(val) => return ControlFlow::Return(val),
                }
            },

            ast::Stmt::For(ast::ForStatement {
                var,
                ty: _,
                expr,
                body,
            }) => {
                let (from, to, inclusive) = match &expr.thing {
                    ast::Expr::Range(ast::RangeExpr {
                        from,
                        to,
                        inclusive,
                    }) => (from, to, inclusive),
                    _ => panic!(
                        "Interpreter only supports for loops with a range expression in the head"
                    ),
                };

                let from = eval(w, pgm, heap, locals, from);
                debug_assert_eq!(heap[from], I32_TYPE_TAG);
                let from = heap[from + 1] as i32;

                let to = eval(w, pgm, heap, locals, to);
                debug_assert_eq!(heap[to], I32_TYPE_TAG);
                let to = heap[to + 1] as i32;

                if *inclusive {
                    for i in from..=to {
                        let iter_value = heap.allocate_i32(i);
                        locals.insert(var.clone(), iter_value);
                        match exec(w, pgm, heap, locals, body) {
                            ControlFlow::Next(_) => {}
                            ControlFlow::Return(val) => {
                                locals.remove(var);
                                return ControlFlow::Return(val);
                            }
                        }
                    }
                } else {
                    for i in from..to {
                        let iter_value = heap.allocate_i32(i);
                        locals.insert(var.clone(), iter_value);
                        match exec(w, pgm, heap, locals, body) {
                            ControlFlow::Next(_) => {}
                            ControlFlow::Return(val) => {
                                locals.remove(var);
                                return ControlFlow::Return(val);
                            }
                        }
                    }
                }

                locals.remove(var);
                0
            }

            ast::Stmt::Return(expr) => {
                return ControlFlow::Return(eval(w, pgm, heap, locals, expr))
            }
        };
    }

    ControlFlow::Next(return_value)
}

fn eval<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    locals: &mut Map<SmolStr, u64>,
    expr: &L<ast::Expr>,
) -> u64 {
    match &expr.thing {
        ast::Expr::Var(var) => match locals.get(var) {
            Some(value) => *value,
            None => match pgm.top_level_funs.get(var) {
                Some(top_fun) => heap.allocate_top_fun(top_fun.idx),
                None => panic!("{}: unbound variable: {}", LocDisplay(expr.start), var),
            },
        },

        ast::Expr::UpperVar(ty_name) => {
            let ty_con = pgm.ty_cons.get(ty_name).unwrap();
            let ty_tag = ty_con.type_tag;
            let (first_tag, last_tag) = ty_con.tag_range();
            assert_eq!(first_tag, last_tag);
            heap.allocate_constr(ty_tag)
        }

        ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field }) => {
            let object = eval(w, pgm, heap, locals, object);
            let object_tag = heap[object];
            let fields = pgm.get_tag_fields(object_tag);
            match fields {
                Fields::Unnamed(_) => panic!(
                    "FieldSelect of {} with unnamed fields, field = {} ({:?})",
                    object_tag, field, expr.start,
                ),
                Fields::Named(fields) => {
                    let (field_idx, _) = fields
                        .iter()
                        .enumerate()
                        .find(|(_, field_)| *field_ == field)
                        .unwrap();
                    heap[object + 1 + (field_idx as u64)]
                }
            }
        }

        ast::Expr::ConstrSelect(ast::ConstrSelectExpr {
            ty,
            constr: constr_name,
        }) => {
            let ty_con = pgm.ty_cons.get(ty).unwrap();
            let (constr_idx, constr) = ty_con
                .value_constrs
                .iter()
                .enumerate()
                .find(|(_constr_idx, constr)| constr.name.as_ref().unwrap() == constr_name)
                .unwrap();
            let tag = ty_con.type_tag + (constr_idx as u64);
            if constr.fields.is_empty() {
                let addr = heap.allocate(1);
                heap[addr] = tag;
                addr
            } else {
                heap.allocate_constr(tag)
            }
        }

        ast::Expr::Call(ast::CallExpr { fun, args }) => {
            // See if `fun` is a method or function and avoid tear-off allocations for
            // performance (and also because we don't support method tear-offs right now).
            let fun: u64 = match &fun.thing {
                ast::Expr::Var(var) => match locals.get(var) {
                    Some(val) => *val,
                    None => match pgm.top_level_funs.get(var) {
                        Some(fun) => {
                            let arg_values = args
                                .iter()
                                .map(|arg| eval(w, pgm, heap, locals, &arg.expr))
                                .collect();
                            return call(w, pgm, heap, fun, arg_values, expr.start);
                        }
                        None => eval(w, pgm, heap, locals, fun),
                    },
                },

                ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field }) => {
                    if let ast::Expr::UpperVar(ty) = &object.thing {
                        let ty_con = pgm
                            .ty_cons
                            .get(ty)
                            .unwrap_or_else(|| panic!("Undefined type: {}", ty));

                        // Handle `Type.Constructor`.
                        if field.chars().next().unwrap().is_uppercase() {
                            return allocate_object_from_names(
                                w,
                                pgm,
                                heap,
                                locals,
                                ty,
                                Some(field.clone()),
                                args,
                                expr.start,
                            );
                        } else {
                            // Handle `Type.associatedFunction`.
                            let fun = pgm.associated_funs[ty_con.type_tag as usize]
                                .get(field)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "Type {} does not have associated function {}",
                                        ty, field
                                    )
                                });

                            let args: Vec<u64> = args
                                .iter()
                                .map(|arg| eval(w, pgm, heap, locals, &arg.expr))
                                .collect();

                            return call(w, pgm, heap, fun, args, expr.start);
                        }
                    }

                    let object = eval(w, pgm, heap, locals, object);
                    let object_tag = heap[object];
                    let fun = pgm.associated_funs[object_tag as usize]
                        .get(field)
                        .unwrap_or_else(|| {
                            panic!(
                                "{}: Object with tag {} doesn't have field or method {:?}",
                                LocDisplay(expr.start),
                                object_tag,
                                field
                            )
                        });
                    let mut args: Vec<u64> = args
                        .iter()
                        .map(|arg| eval(w, pgm, heap, locals, &arg.expr))
                        .collect();
                    args.insert(0, object);
                    return call(w, pgm, heap, fun, args, expr.start);
                }

                ast::Expr::UpperVar(ty) => {
                    return allocate_object_from_names(
                        w, pgm, heap, locals, ty, None, args, expr.start,
                    );
                }

                ast::Expr::ConstrSelect(_)
                | ast::Expr::Call(_)
                | ast::Expr::Int(_)
                | ast::Expr::String(_)
                | ast::Expr::Self_
                | ast::Expr::BinOp(_)
                | ast::Expr::UnOp(_)
                | ast::Expr::ArrayIndex(_)
                | ast::Expr::Record(_)
                | ast::Expr::Range(_) => eval(w, pgm, heap, locals, fun),
            };

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
                        arg_values.push(eval(w, pgm, heap, locals, &arg.expr));
                    }
                    call(w, pgm, heap, top_fun, arg_values, expr.start)
                }

                ASSOC_FUN_TYPE_TAG => {
                    let _ty_tag = heap[fun + 1];
                    let _fun_tag = heap[fun + 2];
                    todo!()
                }

                _ => panic!("Function evaluated to non-callable"),
            }
        }

        ast::Expr::Int(i) => heap.allocate_i32(*i),

        ast::Expr::String(parts) => {
            let mut bytes: Vec<u8> = vec![];
            for part in parts {
                match part {
                    StringPart::Str(str) => bytes.extend(str.as_bytes()),
                    StringPart::Expr(expr) => {
                        let part_val = eval(w, pgm, heap, locals, expr);
                        // Call toStr
                        let part_str_val = call_method(
                            w,
                            pgm,
                            heap,
                            part_val,
                            &"toStr".into(),
                            vec![],
                            expr.start,
                        );
                        assert_eq!(heap[part_str_val], STR_TYPE_TAG);
                        let part_bytes = heap.str_bytes(part_str_val);
                        bytes.extend(part_bytes);
                    }
                }
            }
            heap.allocate_str(&bytes)
        }

        ast::Expr::Self_ => *locals.get("self").unwrap(),

        ast::Expr::BinOp(ast::BinOpExpr { left, right, op }) => {
            let left = eval(w, pgm, heap, locals, left);
            let right = eval(w, pgm, heap, locals, right);

            let method_name = match op {
                ast::BinOp::Add => "__add",
                ast::BinOp::Subtract => "__sub",
                ast::BinOp::Multiply => "__mul",
                ast::BinOp::Equal => {
                    let eq = eq(w, pgm, heap, left, right, expr.start);
                    return pgm.bool_alloc(eq);
                }
                ast::BinOp::NotEqual => {
                    let eq = eq(w, pgm, heap, left, right, expr.start);
                    return pgm.bool_alloc(!eq);
                }
                ast::BinOp::Lt => {
                    let ord = cmp(w, pgm, heap, left, right, expr.start);
                    return pgm.bool_alloc(matches!(ord, Ordering::Less));
                }
                ast::BinOp::Gt => {
                    let ord = cmp(w, pgm, heap, left, right, expr.start);
                    return pgm.bool_alloc(matches!(ord, Ordering::Greater));
                }
                ast::BinOp::LtEq => {
                    let ord = cmp(w, pgm, heap, left, right, expr.start);
                    return pgm.bool_alloc(matches!(ord, Ordering::Less | Ordering::Equal));
                }
                ast::BinOp::GtEq => {
                    let ord = cmp(w, pgm, heap, left, right, expr.start);
                    return pgm.bool_alloc(matches!(ord, Ordering::Greater | Ordering::Equal));
                }
                ast::BinOp::And => "__and",
                ast::BinOp::Or => "__or",
            };

            call_method(
                w,
                pgm,
                heap,
                left,
                &method_name.into(),
                vec![right],
                expr.start,
            )
        }

        ast::Expr::UnOp(ast::UnOpExpr { op, expr }) => {
            let val = eval(w, pgm, heap, locals, expr);
            assert!(heap[val] <= TRUE_TYPE_TAG);

            match op {
                ast::UnOp::Not => pgm.bool_alloc(heap[val] == FALSE_TYPE_TAG),
            }
        }

        ast::Expr::ArrayIndex(ast::ArrayIndexExpr { array, index }) => {
            let array = eval(w, pgm, heap, locals, array);
            let index_boxed = eval(w, pgm, heap, locals, index);
            let index = heap[index_boxed + 1];
            let array_len = heap[array + 1];
            if index >= array_len {
                panic!("OOB array access, len = {}, index = {}", array_len, index);
            }
            heap[array + 2 + index]
        }

        ast::Expr::Record(exprs) => {
            let shape = RecordShape::from_named_things(exprs);
            let type_tag = *pgm.record_ty_tags.get(&shape).unwrap();

            let record = heap.allocate(exprs.len() + 1);
            heap[record] = type_tag;

            if !exprs.is_empty() && exprs[0].name.is_some() {
                heap[record] = type_tag;

                let mut names: Vec<SmolStr> = exprs
                    .iter()
                    .map(|ast::Named { name, thing: _ }| name.as_ref().unwrap().clone())
                    .collect();
                names.sort();

                for (name_idx, name_) in names.iter().enumerate() {
                    let expr = exprs
                        .iter()
                        .find_map(|ast::Named { name, thing }| {
                            if name.as_ref().unwrap() == name_ {
                                Some(thing)
                            } else {
                                None
                            }
                        })
                        .unwrap();

                    let value = eval(w, pgm, heap, locals, expr);
                    heap[record + (name_idx as u64) + 1] = value;
                }
            } else {
                for (idx, ast::Named { name: _, thing }) in exprs.iter().enumerate() {
                    let value = eval(w, pgm, heap, locals, thing);
                    heap[record + (idx as u64) + 1] = value;
                }
            }

            record
        }

        ast::Expr::Range(_) => {
            panic!("Interpreter only supports range expressions in for loops")
        }
    }
}

fn assign<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    locals: &mut Map<SmolStr, u64>,
    lhs: &ast::L<ast::Expr>,
    val: u64,
    op: ast::AssignOp,
    loc: Loc,
) {
    match &lhs.thing {
        ast::Expr::Var(var) => match op {
            ast::AssignOp::Eq => {
                let old = locals.insert(var.clone(), val);
                assert!(old.is_some());
            }
            ast::AssignOp::PlusEq => todo!(),
            ast::AssignOp::MinusEq => todo!(),
        },
        ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field }) => {
            let object = eval(w, pgm, heap, locals, object);
            let object_tag = heap[object];
            let object_con = &pgm.cons_by_tag[object_tag as usize];
            let object_fields = &object_con.fields;
            let field_idx = object_fields.find_named_field_idx(field);
            let new_val = match op {
                ast::AssignOp::Eq => val,
                ast::AssignOp::PlusEq => {
                    let field_value = heap[object + 1 + field_idx];
                    call_method(w, pgm, heap, field_value, &"__add".into(), vec![val], loc)
                }
                ast::AssignOp::MinusEq => {
                    let field_value = heap[object + 1 + field_idx];
                    call_method(w, pgm, heap, field_value, &"__sub".into(), vec![val], loc)
                }
            };
            heap[object + 1 + field_idx] = new_val;
        }
        _ => todo!("Assign statement with fancy LHS at {:?}", lhs.start),
    }
}

fn cmp<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    val1: u64,
    val2: u64,
    loc: Loc,
) -> Ordering {
    let ret = call_method(w, pgm, heap, val1, &"__cmp".into(), vec![val2], loc);
    let ret_tag = heap[ret];
    let ordering_ty_con = pgm
        .ty_cons
        .get("Ordering")
        .unwrap_or_else(|| panic!("__cmp was called, but the Ordering type is not defined"));

    assert_eq!(ordering_ty_con.value_constrs.len(), 3);
    let (less_tag, _) = ordering_ty_con.get_constr_with_tag("Less");
    let (eq_tag, _) = ordering_ty_con.get_constr_with_tag("Equal");
    let (greater_tag, _) = ordering_ty_con.get_constr_with_tag("Greater");

    if ret_tag == less_tag {
        Ordering::Less
    } else if ret_tag == eq_tag {
        Ordering::Equal
    } else if ret_tag == greater_tag {
        Ordering::Greater
    } else {
        panic!()
    }
}

fn eq<W: Write>(w: &mut W, pgm: &Pgm, heap: &mut Heap, val1: u64, val2: u64, loc: Loc) -> bool {
    let ret = call_method(w, pgm, heap, val1, &"__eq".into(), vec![val2], loc);
    let ret_tag = heap[ret];

    debug_assert!(matches!(ret_tag, TRUE_TYPE_TAG | FALSE_TYPE_TAG));
    ret_tag == TRUE_TYPE_TAG
}

// NB. Because we don't have a proper type system yet, this doesn't assume that the program is
// well-typed and check the constructor tag even when matching a product type.
//
// TODO: It would be simpler to clone the env before `bind_pattern` and restore it if binding
// fails.
fn test_pattern(
    pgm: &Pgm,
    heap: &Heap,
    locals: &Map<SmolStr, u64>,
    pattern: &L<ast::Pat>,
    value: u64,
) -> bool {
    match &pattern.thing {
        ast::Pat::Var(_) | ast::Pat::Ignore => true,

        ast::Pat::Constr(ast::ConstrPattern {
            constr: ast::Constructor { type_, constr },
            fields: field_pats,
        }) => {
            let value_tag = heap[value];

            let ty_con = pgm.ty_cons.get(type_).unwrap();
            let (ty_con_first_tag, ty_con_last_tag) = ty_con.tag_range();

            if value_tag < ty_con_first_tag || value_tag > ty_con_last_tag {
                eprintln!("TYPE ERROR: Value type doesn't match type constructor type tag in pattern match");
                eprintln!(
                    "  value tag = {}, ty con first tag = {}, ty con last tag = {}",
                    value_tag, ty_con_first_tag, ty_con_last_tag
                );
                return false;
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
                        return false;
                    }
                    0
                }
            };

            if value_tag != ty_con.type_tag + (constr_idx as u64) {
                return false;
            }

            let fields = pgm.get_tag_fields(value_tag);
            test_field_patterns(pgm, heap, locals, fields, field_pats, value)
        }

        ast::Pat::Record(fields) => {
            assert!(!fields.is_empty());
            let value_tag = heap[value];
            let value_fields = pgm.get_tag_fields(value_tag);

            match value_fields {
                Fields::Unnamed(arity) => {
                    for i in 0..*arity {
                        if !test_pattern(
                            pgm,
                            heap,
                            locals,
                            &fields[i as usize].thing,
                            heap[value + 1 + (i as u64)],
                        ) {
                            return false;
                        }
                    }
                }

                Fields::Named(names) => {
                    for (field_idx, field_name) in names.iter().enumerate() {
                        let field_value = heap[value + 1 + (field_idx as u64)];
                        let field_pattern = fields
                            .iter()
                            .find(|field| field.name.as_ref().unwrap() == field_name)
                            .unwrap();
                        if !test_pattern(pgm, heap, locals, &field_pattern.thing, field_value) {
                            return false;
                        }
                    }
                }
            }

            true
        }

        ast::Pat::StrPfx(pfx, _var) => {
            debug_assert!(matches!(heap[value], STR_TYPE_TAG | STR_VIEW_TYPE_TAG));
            let value_bytes = if heap[value] == STR_TYPE_TAG {
                heap.str_bytes(value)
            } else {
                heap.str_view_bytes(value)
            };
            value_bytes.starts_with(pfx.as_bytes())
        }

        ast::Pat::Str(str) => {
            debug_assert!(matches!(heap[value], STR_TYPE_TAG | STR_VIEW_TYPE_TAG));
            let value_bytes = if heap[value] == STR_TYPE_TAG {
                heap.str_bytes(value)
            } else {
                heap.str_view_bytes(value)
            };
            value_bytes == str.as_bytes()
        }
    }
}

fn test_field_patterns(
    pgm: &Pgm,
    heap: &Heap,
    locals: &Map<SmolStr, u64>,
    constr_fields: &Fields,
    field_pats: &[ast::Named<Box<L<ast::Pat>>>],
    value: u64,
) -> bool {
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
                if !test_pattern(pgm, heap, locals, &field_pat.thing, field_value) {
                    return false;
                }
            }
        }

        Fields::Named(field_tys) => {
            assert_eq!(
                field_tys.len(),
                field_pats.len(),
                "Pattern number of fields doesn't match value number of fields"
            );
            for (field_idx, field_name) in field_tys.iter().enumerate() {
                let field_pattern = field_pats
                    .iter()
                    .find(|field| field.name.as_ref().unwrap() == field_name)
                    .unwrap();

                if !test_pattern(
                    pgm,
                    heap,
                    locals,
                    &field_pattern.thing,
                    heap[value + 1 + field_idx as u64],
                ) {
                    return false;
                }
            }
        }
    }

    true
}

fn bind_pattern(
    pgm: &Pgm,
    heap: &mut Heap,
    locals: &mut Map<SmolStr, u64>,
    pattern: &L<ast::Pat>,
    value: u64,
) {
    match &pattern.thing {
        ast::Pat::Var(var) => {
            locals.insert(var.clone(), value);
        }

        ast::Pat::Constr(ast::ConstrPattern { constr, fields }) => {
            if cfg!(debug_assertions) {
                let ty = pgm.ty_cons.get(&constr.type_).unwrap();
                let (first_tag, last_tag) = ty.tag_range();
                assert!(first_tag <= heap[value] && heap[value] <= last_tag);
            }
            for (field_pattern_idx, field_pattern) in fields.iter().enumerate() {
                let field_value = heap[value + 1 + (field_pattern_idx as u64)];
                bind_pattern(pgm, heap, locals, &field_pattern.thing, field_value);
            }
        }

        ast::Pat::Record(fields) => {
            assert!(!fields.is_empty());
            match fields[0].name {
                Some(_) => {
                    // <name> = <pattern>, where `name`s are the record field names. Record
                    // shapes have ordered names, so sort the names first before looking up the
                    // shape.
                    // TODO: Do this before the interpreter to avoid repeating it.
                    let mut patterns = fields.clone();
                    patterns.sort_by(|field1, field2| {
                        field1
                            .name
                            .as_ref()
                            .unwrap()
                            .cmp(field2.name.as_ref().unwrap())
                    });

                    if cfg!(debug_assertions) {
                        let shape = RecordShape::from_named_things(&patterns);
                        let type_tag = *pgm.record_ty_tags.get(&shape).unwrap();
                        assert_eq!(type_tag, heap[value]);
                    }

                    for (pattern_idx, pattern) in patterns.iter().enumerate() {
                        bind_pattern(
                            pgm,
                            heap,
                            locals,
                            &pattern.thing,
                            heap[value + 1 + (pattern_idx as u64)],
                        );
                    }
                }
                None => {
                    // TODO: Check shape
                    for (pattern_idx, pattern) in fields.iter().enumerate() {
                        bind_pattern(
                            pgm,
                            heap,
                            locals,
                            &pattern.thing,
                            heap[value + 1 + (pattern_idx as u64)],
                        );
                    }
                }
            }
        }

        ast::Pat::StrPfx(pfx, var) => {
            let pfx_len = pfx.len();
            let rest = if heap[value] == STR_TYPE_TAG {
                let len = heap.str_bytes(value).len();
                heap.allocate_str_view(value, pfx_len as u64, len as u64)
            } else {
                let len = heap.str_view_bytes(value).len();
                heap.allocate_str_view_from_str_view(value, pfx_len as u64, len as u64)
            };
            locals.insert(var.clone(), rest);
        }

        ast::Pat::Ignore | ast::Pat::Str(_) => {}
    }
}

fn obj_to_string(pgm: &Pgm, heap: &Heap, obj: u64, loc: Loc) -> String {
    use std::fmt::Write;

    let mut s = String::new();

    let tag = heap[obj];
    let con = &pgm.cons_by_tag[tag as usize];

    write!(&mut s, "{}: ", LocDisplay(loc)).unwrap();

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

struct LocDisplay(Loc);

impl std::fmt::Display for LocDisplay {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.0.line + 1, self.0.col + 1)
    }
}
