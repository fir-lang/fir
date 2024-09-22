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

use crate::ast::{self, Id, Loc, L};
use crate::collections::{Map, Set};
use crate::interpolation::StringPart;
use crate::record_collector::{collect_records, RecordShape};

use std::cmp::Ordering;
use std::io::Write;

use bytemuck::cast_slice_mut;
use smol_str::SmolStr;

pub fn run<W: Write>(w: &mut W, pgm: Vec<L<ast::TopDecl>>, input: &str) {
    let mut heap = Heap::new();
    let pgm = Pgm::new(pgm, &mut heap);

    // Allocate command line arguments to be passed to the program.
    let input = heap.allocate_str(pgm.str_ty_tag, input.as_bytes());

    // Find the main function.
    let main_fun = pgm
        .top_level_funs
        .get("main")
        .unwrap_or_else(|| panic!("main function not defined"));
    call(
        w,
        &pgm,
        &mut heap,
        main_fun,
        vec![input],
        // `main` doesn't have a call site, called by the interpreter.
        &Loc {
            module: "".into(),
            line_start: 0,
            col_start: 0,
            byte_offset_start: 0,
            line_end: 0,
            col_end: 0,
            byte_offset_end: 0,
        },
    );
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
    METHOD_TYPE_TAG,    // Methdo closure, e.g. `x.toString`.
    FIRST_TYPE_TAG,     // First available type tag for user types.
);

#[derive(Debug, Default)]
struct Pgm {
    /// Type constructors by type name.
    ///
    /// These don't include records.
    ///
    /// This can be used when allocating.
    ty_cons: Map<Id, TyCon>,

    /// Maps object tags to constructor info.
    cons_by_tag: Vec<Con>,

    /// Type tags of records.
    ///
    /// This can be used to get the tag of a record, from a record pattern, value, or type.
    record_ty_tags: Map<RecordShape, u64>,

    /// Associated functions, indexed by type tag, then function name.
    associated_funs: Vec<Map<Id, Fun>>,

    /// Associated functions, indexed by type tag, then function index.
    associated_funs_by_idx: Vec<Vec<Fun>>,

    /// Top-level functions, indexed by function name.
    top_level_funs: Map<Id, Fun>,

    /// Same as `top_level_funs`, but indexed by the function index.
    top_level_funs_by_idx: Vec<Fun>,

    // Some allocations and type tags for the built-ins.
    true_alloc: u64,
    false_alloc: u64,
    char_ty_tag: u64,
    str_ty_tag: u64,
    str_view_ty_tag: u64,
    i32_ty_tag: u64,
    u32_ty_tag: u64,
    i8_ty_tag: u64,
    u8_ty_tag: u64,
    array_ty_tag: u64,
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
        ty_name: Id,
        con_name: Option<Id>,
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

const INITIAL_HEAP_SIZE_WORDS: usize = (1024 * 1024 * 1024) / 8; // 1 GiB

#[derive(Debug)]
enum ControlFlow {
    /// Continue with the next statement.
    Val(u64),

    /// Return value from the function.
    Ret(u64),
}

macro_rules! val {
    ($expr:expr) => {
        match $expr {
            ControlFlow::Val(val) => val,
            ControlFlow::Ret(val) => return ControlFlow::Ret(val),
        }
    };
}

impl Pgm {
    fn new(pgm: Vec<L<ast::TopDecl>>, heap: &mut Heap) -> Pgm {
        // Initialize `ty_cons`.
        let (ty_cons, mut next_type_tag): (Map<Id, TyCon>, u64) = init::collect_types(&pgm);

        fn convert_record(shape: &RecordShape) -> Fields {
            match shape {
                RecordShape::UnnamedFields { arity } => Fields::Unnamed(*arity),
                RecordShape::NamedFields { fields } => Fields::Named(fields.clone()),
            }
        }

        let mut cons_by_tag: Vec<Con> = vec![];

        let mut ty_cons_sorted: Vec<(Id, TyCon)> = ty_cons
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

        let mut associated_funs_vec: Vec<Map<Id, Fun>> =
            vec![Default::default(); next_type_tag as usize];

        let mut associated_funs_by_idx: Vec<Vec<Fun>> =
            vec![Default::default(); next_type_tag as usize];

        for (ty_name, funs) in associated_funs {
            let ty_con = ty_cons
                .get(&ty_name)
                .unwrap_or_else(|| panic!("Type not defined: {}", ty_name));
            let first_tag = ty_cons.get(&ty_name).unwrap().type_tag as usize;
            let n_constrs = ty_con.value_constrs.len();

            let mut funs_as_vec: Vec<Fun> = funs.values().cloned().collect();
            funs_as_vec.sort_by_key(|fun| fun.idx);

            if n_constrs == 0 {
                // A built-in type with no constructor.
                associated_funs_vec[first_tag] = funs;
                associated_funs_by_idx[first_tag] = funs_as_vec;
            } else {
                for tag in first_tag..first_tag + n_constrs {
                    associated_funs_vec[tag].clone_from(&funs);
                    associated_funs_by_idx[tag] = funs_as_vec.clone();
                }
            }
        }

        // Initialize `top_level_funs_by_idx`.
        let mut top_level_funs_vec: Vec<(Id, Fun)> = top_level_funs
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();

        top_level_funs_vec.sort_by_key(|(_, fun)| fun.idx);

        let top_level_funs_by_idx = top_level_funs_vec.into_iter().map(|(_, f)| f).collect();

        let bool_ty_con: &TyCon = ty_cons.get("Bool").as_ref().unwrap();
        assert_eq!(bool_ty_con.value_constrs[0].name, Some(Id::new("False")));
        assert_eq!(bool_ty_con.value_constrs[1].name, Some(Id::new("True")));

        let false_alloc = cons_by_tag[bool_ty_con.type_tag as usize].alloc.unwrap();
        let true_alloc = cons_by_tag[bool_ty_con.type_tag as usize + 1]
            .alloc
            .unwrap();

        let char_ty_tag = ty_cons.get("Char").as_ref().unwrap().type_tag;
        let str_ty_tag = ty_cons.get("Str").as_ref().unwrap().type_tag;
        let str_view_ty_tag = ty_cons.get("StrView").as_ref().unwrap().type_tag;
        let i32_ty_tag = ty_cons.get("I32").as_ref().unwrap().type_tag;
        let u32_ty_tag = ty_cons.get("U32").as_ref().unwrap().type_tag;
        let i8_ty_tag = ty_cons.get("I8").as_ref().unwrap().type_tag;
        let u8_ty_tag = ty_cons.get("U8").as_ref().unwrap().type_tag;
        let array_ty_tag = ty_cons.get("Array").as_ref().unwrap().type_tag;

        Pgm {
            ty_cons,
            cons_by_tag,
            record_ty_tags,
            associated_funs: associated_funs_vec,
            associated_funs_by_idx,
            top_level_funs,
            top_level_funs_by_idx,
            false_alloc,
            true_alloc,
            char_ty_tag,
            str_ty_tag,
            str_view_ty_tag,
            i32_ty_tag,
            u32_ty_tag,
            i8_ty_tag,
            u8_ty_tag,
            array_ty_tag,
        }
    }

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

        impl<'a> std::fmt::Display for TagNameDisplay<'a> {
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
        }
    }
}

fn call<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    fun: &Fun,
    args: Vec<u64>,
    loc: &Loc,
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
    method: &Id,
    mut args: Vec<u64>,
    loc: &Loc,
) -> u64 {
    let tag = heap[receiver];
    let fun = pgm.associated_funs[tag as usize]
        .get(method)
        .unwrap_or_else(|| {
            panic!(
                "{}: Object with type {} (tag {}) does not have {} method",
                LocDisplay(loc),
                pgm.tag_name_display(tag),
                tag,
                method
            )
        });
    args.insert(0, receiver);
    call(w, pgm, heap, fun, args, loc)
}

fn call_source_fun<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    fun: &ast::FunDecl,
    args: Vec<u64>,
    loc: &Loc,
) -> u64 {
    assert_eq!(
        fun.num_params(),
        args.len() as u32,
        "{}, fun: {}",
        LocDisplay(loc),
        fun.sig.name.node
    );

    let mut locals: Map<Id, u64> = Default::default();

    let mut arg_idx: usize = 0;
    if fun.sig.self_ {
        locals.insert(Id::new("self"), args[0]);
        arg_idx += 1;
    }

    for (param_name, _param_type) in &fun.sig.params {
        let old = locals.insert(param_name.clone(), args[arg_idx]);
        assert!(old.is_none());
        arg_idx += 1;
    }

    match exec(w, pgm, heap, &mut locals, &fun.body.as_ref().unwrap().node) {
        ControlFlow::Val(val) | ControlFlow::Ret(val) => val,
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

fn exec<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    locals: &mut Map<Id, u64>,
    stmts: &[L<ast::Stmt>],
) -> ControlFlow {
    let mut return_value: u64 = 0;

    for stmt in stmts {
        return_value = match &stmt.node {
            ast::Stmt::Let(ast::LetStmt { lhs, ty: _, rhs }) => {
                let val = val!(eval(w, pgm, heap, locals, &rhs.node, &rhs.loc));
                match try_bind_pat(pgm, heap, lhs, val) {
                    Some(binds) => locals.extend(binds.into_iter()),
                    None => panic!("Pattern binding at {} failed", LocDisplay(&stmt.loc)),
                }
                val
            }

            ast::Stmt::Assign(ast::AssignStmt { lhs, rhs, op }) => {
                let rhs = val!(eval(w, pgm, heap, locals, &rhs.node, &rhs.loc));
                val!(assign(w, pgm, heap, locals, lhs, rhs, *op, &stmt.loc))
            }

            ast::Stmt::Expr(expr) => val!(eval(w, pgm, heap, locals, &expr.node, &expr.loc)),

            ast::Stmt::While(ast::WhileStmt { cond, body }) => loop {
                let cond = val!(eval(w, pgm, heap, locals, &cond.node, &cond.loc));
                debug_assert!(cond == pgm.true_alloc || cond == pgm.false_alloc);
                if cond == pgm.false_alloc {
                    break 0; // FIXME: Return unit
                }
                match exec(w, pgm, heap, locals, body) {
                    ControlFlow::Val(_val) => {}
                    ControlFlow::Ret(val) => return ControlFlow::Ret(val),
                }
            },

            ast::Stmt::For(ast::ForStmt {
                var,
                ty: _,
                expr,
                body,
            }) => {
                let (from, to, inclusive) = match &expr.node {
                    ast::Expr::Range(ast::RangeExpr {
                        from,
                        to,
                        inclusive,
                    }) => (from, to, inclusive),
                    _ => panic!(
                        "Interpreter only supports for loops with a range expression in the head"
                    ),
                };

                let from = val!(eval(w, pgm, heap, locals, &from.node, &from.loc));
                debug_assert_eq!(heap[from], pgm.i32_ty_tag);
                let from = heap[from + 1] as i32;

                let to = val!(eval(w, pgm, heap, locals, &to.node, &to.loc));
                debug_assert_eq!(heap[to], pgm.i32_ty_tag);
                let to = heap[to + 1] as i32;

                if *inclusive {
                    for i in from..=to {
                        let iter_value = heap.allocate_i32(pgm.i32_ty_tag, i);
                        locals.insert(var.clone(), iter_value);
                        match exec(w, pgm, heap, locals, body) {
                            ControlFlow::Val(_) => {}
                            ControlFlow::Ret(val) => {
                                locals.remove(var);
                                return ControlFlow::Ret(val);
                            }
                        }
                    }
                } else {
                    for i in from..to {
                        let iter_value = heap.allocate_i32(pgm.i32_ty_tag, i);
                        locals.insert(var.clone(), iter_value);
                        match exec(w, pgm, heap, locals, body) {
                            ControlFlow::Val(_) => {}
                            ControlFlow::Ret(val) => {
                                locals.remove(var);
                                return ControlFlow::Ret(val);
                            }
                        }
                    }
                }

                locals.remove(var);
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
    locals: &mut Map<Id, u64>,
    expr: &ast::Expr,
    loc: &Loc,
) -> ControlFlow {
    match expr {
        ast::Expr::Var(var) => match locals.get(var) {
            Some(value) => ControlFlow::Val(*value),
            None => match pgm.top_level_funs.get(var) {
                Some(top_fun) => ControlFlow::Val(heap.allocate_top_fun(top_fun.idx)),
                None => panic!("{}: Unbound variable: {}", LocDisplay(loc), var),
            },
        },

        ast::Expr::Constr(ty_name) => {
            let ty_con = pgm.ty_cons.get(ty_name).unwrap();
            let ty_tag = ty_con.type_tag;
            let (first_tag, last_tag) = ty_con.tag_range();
            assert_eq!(first_tag, last_tag);
            ControlFlow::Val(heap.allocate_constr(ty_tag))
        }

        ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field }) => {
            let object = val!(eval(w, pgm, heap, locals, &object.node, &object.loc));
            let object_tag = heap[object];

            // This could be a field of method selection. TOOD: Maybe type checker could elaborate?
            // Check fields first.
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

            // Must be a method.
            if let Some(method) = pgm.associated_funs[object_tag as usize].get(field) {
                return ControlFlow::Val(heap.allocate_method(object, method.idx));
            };

            panic!(
                "{}: Unable to select method or field {}",
                LocDisplay(loc),
                field
            );
        }

        ast::Expr::ConstrSelect(ast::ConstrSelectExpr { ty, constr }) => {
            ControlFlow::Val(constr_select(pgm, heap, ty, constr))
        }

        ast::Expr::AssocFnSelect(ast::AssocFnSelectExpr { ty, member }) => {
            let ty_con = pgm.ty_cons.get(ty).unwrap();
            let fun = pgm.associated_funs[ty_con.type_tag as usize]
                .get(member)
                .unwrap();
            ControlFlow::Val(heap.allocate_assoc_fun(ty_con.type_tag, fun.idx))
        }

        ast::Expr::Call(ast::CallExpr { fun, args }) => {
            // See if `fun` is a method or function and avoid tear-off allocations for
            // performance (and also because we don't support method tear-offs right now).
            let fun: u64 = match &fun.node {
                ast::Expr::Var(var) => match locals.get(var) {
                    Some(val) => *val,
                    None => match pgm.top_level_funs.get(var) {
                        Some(fun) => {
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
                            return ControlFlow::Val(call(w, pgm, heap, fun, arg_values, loc));
                        }
                        None => val!(eval(w, pgm, heap, locals, &fun.node, &fun.loc)),
                    },
                },

                ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field }) => {
                    if let ast::Expr::Constr(ty) = &object.node {
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
                                loc,
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

                            return ControlFlow::Val(call(w, pgm, heap, fun, arg_vals, loc));
                        }
                    }

                    let object = val!(eval(w, pgm, heap, locals, &object.node, &object.loc));
                    let object_tag = heap[object];
                    let fun = pgm.associated_funs[object_tag as usize]
                        .get(field)
                        .unwrap_or_else(|| {
                            panic!(
                                "{}: Object with type {} (tag {}) doesn't have field or method {:?}",
                                LocDisplay(loc),
                                pgm.tag_name_display(object_tag),
                                object_tag,
                                field
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
                    arg_vals.insert(0, object);
                    return ControlFlow::Val(call(w, pgm, heap, fun, arg_vals, loc));
                }

                ast::Expr::Constr(ty) => {
                    return allocate_object_from_names(w, pgm, heap, locals, ty, None, args, loc);
                }

                _ => val!(eval(w, pgm, heap, locals, &fun.node, &fun.loc)),
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
                        arg_values.push(val!(eval(
                            w,
                            pgm,
                            heap,
                            locals,
                            &arg.expr.node,
                            &arg.expr.loc
                        )));
                    }
                    ControlFlow::Val(call(w, pgm, heap, top_fun, arg_values, loc))
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
                    ControlFlow::Val(call(w, pgm, heap, fun, arg_values, loc))
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
                    ControlFlow::Val(call(w, pgm, heap, fun, arg_values, loc))
                }

                _ => panic!("Function evaluated to non-callable"),
            }
        }

        ast::Expr::Int(i) => match i {
            ast::IntExpr::I8(val) => ControlFlow::Val(heap.allocate_i8(pgm.i8_ty_tag, *val)),
            ast::IntExpr::U8(val) => ControlFlow::Val(heap.allocate_u8(pgm.u8_ty_tag, *val)),
            ast::IntExpr::I32(val) => ControlFlow::Val(heap.allocate_i32(pgm.i32_ty_tag, *val)),
            ast::IntExpr::U32(val) => ControlFlow::Val(heap.allocate_u32(pgm.u32_ty_tag, *val)),
        },

        ast::Expr::String(parts) => {
            let mut bytes: Vec<u8> = vec![];
            for part in parts {
                match part {
                    StringPart::Str(str) => bytes.extend(str.as_bytes()),
                    StringPart::Expr(expr) => {
                        let part_val = val!(eval(w, pgm, heap, locals, &expr.node, &expr.loc));
                        // Call toStr
                        let part_str_val =
                            call_method(w, pgm, heap, part_val, &"toStr".into(), vec![], &expr.loc);
                        assert_eq!(heap[part_str_val], pgm.str_ty_tag);
                        let part_bytes = heap.str_bytes(part_str_val);
                        bytes.extend(part_bytes);
                    }
                }
            }
            ControlFlow::Val(heap.allocate_str(pgm.str_ty_tag, &bytes))
        }

        ast::Expr::Self_ => ControlFlow::Val(*locals.get("self").unwrap()),

        ast::Expr::BinOp(ast::BinOpExpr { left, right, op }) => {
            let left = val!(eval(w, pgm, heap, locals, &left.node, &left.loc));
            let right = val!(eval(w, pgm, heap, locals, &right.node, &right.loc));

            let method_name = match op {
                ast::BinOp::Add => "__add",
                ast::BinOp::Subtract => "__sub",
                ast::BinOp::Multiply => "__mul",
                ast::BinOp::Equal => {
                    let eq = eq(w, pgm, heap, left, right, loc);
                    return ControlFlow::Val(pgm.bool_alloc(eq));
                }
                ast::BinOp::NotEqual => {
                    let eq = eq(w, pgm, heap, left, right, loc);
                    return ControlFlow::Val(pgm.bool_alloc(!eq));
                }
                ast::BinOp::Lt => {
                    let ord = cmp(w, pgm, heap, left, right, loc);
                    return ControlFlow::Val(pgm.bool_alloc(matches!(ord, Ordering::Less)));
                }
                ast::BinOp::Gt => {
                    let ord = cmp(w, pgm, heap, left, right, loc);
                    return ControlFlow::Val(pgm.bool_alloc(matches!(ord, Ordering::Greater)));
                }
                ast::BinOp::LtEq => {
                    let ord = cmp(w, pgm, heap, left, right, loc);
                    return ControlFlow::Val(
                        pgm.bool_alloc(matches!(ord, Ordering::Less | Ordering::Equal)),
                    );
                }
                ast::BinOp::GtEq => {
                    let ord = cmp(w, pgm, heap, left, right, loc);
                    return ControlFlow::Val(
                        pgm.bool_alloc(matches!(ord, Ordering::Greater | Ordering::Equal)),
                    );
                }
                ast::BinOp::And => "__and",
                ast::BinOp::Or => "__or",
            };

            ControlFlow::Val(call_method(
                w,
                pgm,
                heap,
                left,
                &method_name.into(),
                vec![right],
                loc,
            ))
        }

        ast::Expr::UnOp(ast::UnOpExpr { op, expr }) => {
            let val = val!(eval(w, pgm, heap, locals, &expr.node, &expr.loc));
            debug_assert!(val == pgm.true_alloc || val == pgm.false_alloc);

            match op {
                ast::UnOp::Not => ControlFlow::Val(pgm.bool_alloc(val == pgm.false_alloc)),
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

        ast::Expr::Range(_) => {
            panic!("Interpreter only supports range expressions in for loops")
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
            panic!("Non-exhaustive pattern match");
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
            let i32 = heap.allocate_i32(pgm.u32_ty_tag, (*char as u32) as i32);
            let alloc = heap.allocate(2);
            heap[alloc] = pgm.char_ty_tag;
            heap[alloc + 1] = i32;
            ControlFlow::Val(alloc)
        }

        ast::Expr::Instantiation(path, _tys) => {
            // TODO: After monomorphisation seeing an instantiation node should be a bug.
            match path {
                ast::Path::TopLevel { fun_id } => match pgm.top_level_funs.get(fun_id) {
                    Some(top_fun) => ControlFlow::Val(heap.allocate_top_fun(top_fun.idx)),
                    _ => match pgm.ty_cons.get(fun_id) {
                        Some(ty_con) => {
                            let ty_tag = ty_con.type_tag;
                            let (first_tag, last_tag) = ty_con.tag_range();
                            assert_eq!(first_tag, last_tag);
                            ControlFlow::Val(heap.allocate_constr(ty_tag))
                        }
                        None => panic!("{}: Unbound variable {}", LocDisplay(loc), fun_id),
                    },
                },

                ast::Path::Constructor { ty_id, constr_id } => {
                    ControlFlow::Val(constr_select(pgm, heap, ty_id, constr_id))
                }

                ast::Path::AssociatedFn { ty_id, fun_id } => {
                    let ty_con = pgm.ty_cons.get(ty_id).unwrap();
                    let fun = pgm.associated_funs[ty_con.type_tag as usize]
                        .get(fun_id)
                        .unwrap();
                    ControlFlow::Val(heap.allocate_assoc_fun(ty_con.type_tag, fun.idx))
                }

                ast::Path::Method {
                    receiver,
                    receiver_ty: _,
                    method_id,
                } => {
                    let receiver = val!(eval(w, pgm, heap, locals, receiver, loc));
                    let receiver_tag = heap[receiver as u64];
                    let fun = pgm.associated_funs[receiver_tag as usize]
                        .get(method_id)
                        .unwrap_or_else(|| {
                            panic!(
                                "{}: Object with type {} (tag {}) does not have method {}",
                                LocDisplay(loc),
                                pgm.tag_name_display(receiver_tag),
                                receiver_tag,
                                method_id
                            )
                        });
                    ControlFlow::Val(heap.allocate_method(receiver, fun.idx))
                }
            }
        }
    }
}

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

fn assign<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    locals: &mut Map<Id, u64>,
    lhs: &ast::L<ast::Expr>,
    val: u64,
    op: ast::AssignOp,
    loc: &Loc,
) -> ControlFlow {
    match &lhs.node {
        ast::Expr::Var(var) => match op {
            ast::AssignOp::Eq => {
                let old = locals.insert(var.clone(), val);
                assert!(old.is_some());
            }
            ast::AssignOp::PlusEq => {
                let old_val = locals.get(var).unwrap_or_else(|| {
                    panic!("{}: Unbound variable {}", LocDisplay(&lhs.loc), var)
                });
                let new_val = call_method(w, pgm, heap, *old_val, &"__add".into(), vec![val], loc);
                locals.insert(var.clone(), new_val);
            }
            ast::AssignOp::MinusEq => {
                let old_val = locals.get(var).unwrap_or_else(|| {
                    panic!("{}: Unbound variable {}", LocDisplay(&lhs.loc), var)
                });
                let new_val = call_method(w, pgm, heap, *old_val, &"__sub".into(), vec![val], loc);
                locals.insert(var.clone(), new_val);
            }
            ast::AssignOp::StarEq => {
                let old_val = locals.get(var).unwrap_or_else(|| {
                    panic!("{}: Unbound variable {}", LocDisplay(&lhs.loc), var)
                });
                let new_val = call_method(w, pgm, heap, *old_val, &"__mul".into(), vec![val], loc);
                locals.insert(var.clone(), new_val);
            }
        },
        ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field }) => {
            let object = val!(eval(w, pgm, heap, locals, &object.node, &object.loc));
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
                ast::AssignOp::StarEq => {
                    let field_value = heap[object + 1 + field_idx];
                    call_method(w, pgm, heap, field_value, &"__mul".into(), vec![val], loc)
                }
            };
            heap[object + 1 + field_idx] = new_val;
        }
        _ => todo!("Assign statement with fancy LHS at {:?}", &lhs.loc),
    }
    ControlFlow::Val(val)
}

fn cmp<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    val1: u64,
    val2: u64,
    loc: &Loc,
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

fn eq<W: Write>(w: &mut W, pgm: &Pgm, heap: &mut Heap, val1: u64, val2: u64, loc: &Loc) -> bool {
    let ret = call_method(w, pgm, heap, val1, &"__eq".into(), vec![val2], loc);
    debug_assert!(ret == pgm.true_alloc || ret == pgm.false_alloc);
    ret == pgm.true_alloc
}

fn try_bind_field_pats(
    pgm: &Pgm,
    heap: &mut Heap,
    constr_fields: &Fields,
    field_pats: &[ast::Named<Box<L<ast::Pat>>>],
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

/// Tries to match a pattern. On successful match, returns a map with variables bound in the
/// pattern. On failure returns `None`.
///
/// `heap` argument is `mut` to be able to allocate `StrView`s in string prefix patterns. In the
/// compiled version `StrView`s will be allocated on stack.
fn try_bind_pat(
    pgm: &Pgm,
    heap: &mut Heap,
    pattern: &L<ast::Pat>,
    value: u64,
) -> Option<Map<Id, u64>> {
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

        ast::Pat::Str(str) => {
            debug_assert!(heap[value] == pgm.str_ty_tag || heap[value] == pgm.str_view_ty_tag);
            let value_bytes = if heap[value] == pgm.str_ty_tag {
                heap.str_bytes(value)
            } else {
                heap.str_view_bytes(value)
            };
            if value_bytes == str.as_bytes() {
                Some(Default::default())
            } else {
                None
            }
        }

        ast::Pat::StrPfx(pfx, var) => {
            debug_assert!(heap[value] == pgm.str_ty_tag || heap[value] == pgm.str_view_ty_tag);
            let value_bytes = if heap[value] == pgm.str_ty_tag {
                heap.str_bytes(value)
            } else {
                heap.str_view_bytes(value)
            };
            if value_bytes.starts_with(pfx.as_bytes()) {
                let pfx_len = pfx.len();
                let rest = if heap[value] == pgm.str_ty_tag {
                    let len = heap.str_bytes(value).len();
                    heap.allocate_str_view(pgm.str_view_ty_tag, value, pfx_len as u64, len as u64)
                } else {
                    let len = heap.str_view_bytes(value).len();
                    heap.allocate_str_view_from_str_view(
                        pgm.str_view_ty_tag,
                        value,
                        pfx_len as u64,
                        len as u64,
                    )
                };
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
            if heap[heap[value + 1] + 1] == u64::from(*char as u32) {
                Some(Default::default())
            } else {
                None
            }
        }
    }
}

fn obj_to_string(pgm: &Pgm, heap: &Heap, obj: u64, loc: &Loc) -> String {
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

struct LocDisplay<'a>(&'a Loc);

impl<'a> std::fmt::Display for LocDisplay<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{}:{}",
            self.0.module,
            self.0.line_start + 1,
            self.0.col_start + 1
        )
    }
}
