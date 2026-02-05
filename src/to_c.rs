/*
TODOs:

- Make sure signed integers wrap on overflow and underflow in a defined way. Update the interpreter
  to do the same. Add tests. (`__builtin_add_overflow` etc.)

  In the future we'll probably trap by default and require explicitly allowing overflowing.
  (`checkedAdd`, `uncheckedAdd` etc.)
*/

use crate::ast::{Id, Loc};
use crate::collections::*;
use crate::lowering::*;
use crate::mono_ast as mono;
use crate::utils::loc_display;

use std::fmt::Write;

macro_rules! w {
    ($($arg:tt)*) => {
        ::core::write!($($arg)*).unwrap()
    };
}

macro_rules! wln {
    ($p:expr, $($arg:tt)*) => {{
        ::core::write!($p, $($arg)*).unwrap();
        $p.nl();
    }};
}

macro_rules! writedoc {
    ($p:expr, $($arg:tt)*) => {{
        ::indoc::writedoc!($p, $($arg)*).unwrap();
    }};
}

/// Code generation context.
struct Cg<'a> {
    pgm: &'a LoweredPgm,

    /// Counter for generating fresh temporary variables.
    temp_counter: u32,
}

impl<'a> Cg<'a> {
    fn fresh_temp(&mut self) -> String {
        let n = self.temp_counter;
        self.temp_counter += 1;
        format!("_t{}", n)
    }
}

pub(crate) fn to_c(pgm: &LoweredPgm, main: &str) -> String {
    let mut p = Printer::default();

    writedoc!(
        p,
        "
        #include <inttypes.h>
        #include <setjmp.h>
        #include <stdbool.h>
        #include <stdint.h>
        #include <stdio.h>
        #include <stdlib.h>
        #include <string.h>

        "
    );

    // Generate structs for sum types. These just have the tag and they're mainly to make code
    // easier to read.
    for (ty_id, ty_arg_map) in &pgm.type_objs {
        for (ty_args, objs) in ty_arg_map.iter() {
            if let TypeObjs::Product { .. } = objs {
                continue;
            }
            w!(p, "// {ty_id}");
            if !ty_args.is_empty() {
                w!(p, "[");
                for (i, ty_arg) in ty_args.iter().enumerate() {
                    if i != 0 {
                        w!(p, ", ");
                    }
                    w!(p, "{ty_arg}");
                }
                w!(p, "]");
            }
            p.nl();
            writedoc!(
                p,
                "typedef struct {{
                    uint64_t tag;
                }} {};",
                sum_struct_name(ty_id, ty_args)
            );
            p.nl();
        }
    }

    let heap_objs_sorted = top_sort(
        &pgm.type_objs,
        &pgm.record_objs,
        &pgm.variant_objs,
        &pgm.heap_objs,
    );
    for scc in &heap_objs_sorted {
        // If SCC has more than one element, forward-declare the structs.
        if scc.len() > 1 {
            for heap_obj_idx in scc {
                match &pgm.heap_objs[heap_obj_idx.as_usize()] {
                    HeapObj::Source(source_con) => {
                        let struct_name = source_con_struct_name(source_con);
                        wln!(p, "typedef struct {struct_name} {struct_name};");
                    }
                    HeapObj::Record(record) => {
                        let struct_name = record_struct_name(record);
                        wln!(p, "typedef struct {struct_name} {struct_name};");
                    }
                    HeapObj::Variant(variant) => {
                        let struct_name = variant_struct_name(variant);
                        wln!(p, "typedef struct {struct_name} {struct_name};");
                    }
                    HeapObj::Builtin(BuiltinConDecl::Array { t }) => {
                        let struct_name = array_struct_name(t, pgm);
                        wln!(p, "typedef struct {struct_name} {struct_name};");
                    }
                    HeapObj::Builtin(builtin) => {
                        panic!("Builtin in SCC: {builtin:?}");
                    }
                }
            }
            p.nl();
        }

        // Generate struct definitions.
        for heap_obj_idx in scc {
            heap_obj_to_c(
                &pgm.heap_objs[heap_obj_idx.as_usize()],
                heap_obj_idx.0,
                pgm,
                &mut p,
            );
            p.nl();
        }
    }

    let array_u8_tag = pgm.array_u8_con_idx.as_u64();
    let array_u64_tag = pgm.array_u64_con_idx.as_u64();
    writedoc!(
        p,
        "
        // Exception handling using setjmp/longjmp
        typedef struct ExnHandler {{
            jmp_buf buf;
            struct ExnHandler* prev;
            void* exn_value;  // pointer to boxed exception value
        }} ExnHandler;

        static ExnHandler* current_exn_handler = NULL;

        static void throw_exn(void* exn) {{
            if (current_exn_handler == NULL) {{
                fprintf(stderr, \"Uncaught exception\\n\");
                exit(1);
            }}
            current_exn_handler->exn_value = exn;
            longjmp(current_exn_handler->buf, 1);
        }}

        static uint32_t get_tag(void* obj) {{
            return (uint32_t)*(uint64_t*)obj;
        }}

        static Array_U64* array_new_u64(uint32_t len) {{
            Array_U64* arr = (Array_U64*)malloc(sizeof(Array_U64) + (len * sizeof(uint64_t)));
            arr->tag = {array_u64_tag};
            arr->data_ptr = (uint64_t*)(arr + 1);
            arr->len = len;
            memset(arr + 1, 0, len * sizeof(uint64_t));
            return arr;
        }}

        // String comparison for pattern matching
        static bool str_eq(Str* s1, const char* str2, size_t len2) {{
            Array_U8* bytes_arr = s1->_0;
            uint32_t len1 = (uint32_t)bytes_arr->len;
            if (len1 != len2) return false;
            uint8_t* data_ptr = (uint8_t*)bytes_arr->data_ptr;
            return memcmp(data_ptr, str2, len1) == 0;
        }}

        // Allocate string from bytes
        static Str* alloc_str(const char* bytes, size_t len) {{
            size_t data_words = (len + 7) / 8;
            Array_U8* arr = malloc(sizeof(Array_U8) + (data_words * sizeof(uint64_t)));
            arr->tag = {array_u8_tag};
            arr->data_ptr = (uint8_t*)(arr + 1);
            arr->len = len;
            memset(arr + 1, 0, data_words * sizeof(uint64_t));

            uint8_t* data_ptr = (uint8_t*)arr->data_ptr;
            memcpy(data_ptr, bytes, len);

            Str* str = (Str*)malloc(sizeof(Str));
            str->_tag = TAG_Str;
            str->_0 = arr;
            return str;
        }}

        // Globals for CLI args
        static int g_argc;
        static char** g_argv;

        "
    );
    p.nl();

    if pgm.closures.iter().any(|c| !c.fvs.is_empty()) {
        wln!(p, "// Closure structs for closures with captures");
        p.nl();
        for (i, closure) in pgm.closures.iter().enumerate() {
            gen_closure_struct(closure, i, pgm, &mut p);
        }
        p.nl();
    }

    for (i, fun) in pgm.funs.iter().enumerate() {
        forward_declare_fun(fun, i, pgm, &mut p);
    }
    p.nl();

    for (i, closure) in pgm.closures.iter().enumerate() {
        forward_declare_closure(closure, i, pgm, &mut p);
    }
    p.nl();

    p.nl();
    w!(
        p,
        "// Statically allocated singletons for nullary constructors"
    );
    p.nl();
    for heap_obj in pgm.heap_objs.iter() {
        match heap_obj {
            HeapObj::Source(source_con) if source_con.fields.is_empty() => {
                let singleton_name = source_con_singleton_name(source_con);
                let struct_name = source_con_struct_name(source_con);
                let tag_name = source_con_tag_name(source_con);
                wln!(
                    p,
                    "static {struct_name} {singleton_name}_data = {{ ._tag = {tag_name} }};",
                );
                wln!(p, "#define {singleton_name} (&{singleton_name}_data)");
            }
            HeapObj::Record(record) if record.fields.is_empty() => {
                let struct_name = record_struct_name(record);
                let tag_name = format!("TAG_{}", struct_name);
                let singleton_name = format!("_singleton_{}", struct_name);
                wln!(
                    p,
                    "static {struct_name} {singleton_name}_data = {{ ._tag = {tag_name} }};",
                );
                wln!(p, "#define {singleton_name} (&{singleton_name}_data)");
            }
            _ => {}
        }
    }
    p.nl();

    w!(
        p,
        "// Statically allocated closure objects for constructors"
    );
    p.nl();
    for (tag, heap_obj) in pgm.heap_objs.iter().enumerate() {
        match heap_obj {
            HeapObj::Source(source_con) if !source_con.fields.is_empty() => {
                w!(p, "static uint64_t _con_closure_{tag}_fun(CLOSURE* self");
                for (i, ty) in source_con.fields.iter().enumerate() {
                    w!(p, ", {} p{i}", c_ty(ty, pgm));
                }
                w!(p, ") {{");
                p.indent();
                p.nl();
                let struct_name = heap_obj_struct_name(pgm, HeapObjIdx(tag as u32));
                let tag_name = heap_obj_tag_name(pgm, HeapObjIdx(tag as u32));
                wln!(p, "{struct_name}* _obj = malloc(sizeof({struct_name}));");
                wln!(p, "_obj->_tag = {tag_name};");
                for i in 0..source_con.fields.len() {
                    wln!(p, "_obj->_{i} = p{i};");
                }
                w!(p, "return (uint64_t)_obj;");
                p.dedent();
                p.nl();
                wln!(p, "}}");

                w!(
                    p,
                    "static CLOSURE _con_closure_{tag}_data = {{ .tag = CLOSURE_TAG, .fun = (void(*)(void))_con_closure_{tag}_fun }};",
                );
                p.nl();

                w!(p, "#define _con_closure_{tag} (&_con_closure_{tag}_data)");
                p.nl();
                p.nl();
            }
            _ => {}
        }
    }
    p.nl();

    w!(
        p,
        "// Statically allocated closure objects for top-level functions"
    );
    p.nl();
    for (i, fun) in pgm.funs.iter().enumerate() {
        w!(
            p,
            "static {} _fun_closure_{i}_fun(CLOSURE* self",
            c_ty(&fun.return_ty, pgm),
        );
        for (i, ty) in fun.params.iter().enumerate() {
            w!(p, ", {} p{i}", c_ty(ty, pgm));
        }
        w!(p, ") {{");
        p.indent();
        p.nl();
        w!(p, "return (({}(*)(", c_ty(&fun.return_ty, pgm));
        for (i, ty) in fun.params.iter().enumerate() {
            if i != 0 {
                w!(p, ", ");
            }
            w!(p, "{}", c_ty(ty, pgm));
        }
        w!(p, "))(_fun_{i}))(");
        for i in 0..fun.params.len() {
            if i != 0 {
                w!(p, ", ");
            }
            w!(p, "p{i}");
        }
        w!(p, ");");
        p.dedent();
        p.nl();
        wln!(p, "}}");

        w!(
            p,
            "static CLOSURE _fun_closure_{i}_data = {{ .tag = CLOSURE_TAG, .fun = (void(*)(void))_fun_closure_{i}_fun }};",
        );
        p.nl();

        w!(p, "#define _fun_closure_{i} (&_fun_closure_{i}_data)");
        p.nl();
        p.nl();
    }
    p.nl();

    let mut cg = Cg {
        pgm,
        temp_counter: 0,
    };

    // Generate built-in functions first. Built-in functions don't depend on each other or source
    // functions, but source functions can depend on built-in functions.
    for (i, fun) in pgm.funs.iter().enumerate() {
        if let FunBody::Builtin(builtin) = &fun.body {
            builtin_fun_to_c(
                builtin,
                &fun.ty_args,
                &fun.params,
                &fun.return_ty,
                &fun.exceptions,
                i,
                pgm,
                &mut p,
            );
            p.nl();
        }
    }

    // Generate source functions after built-in functions as they may depend on built-in functions
    // and built-in functions are not forward-declared.
    for (i, fun) in pgm.funs.iter().enumerate() {
        if let FunBody::Source(source) = &fun.body {
            source_fun_to_c(fun, source, i, &mut cg, &mut p);
            p.nl();
        }
    }

    for (i, closure) in pgm.closures.iter().enumerate() {
        closure_to_c(closure, i, &mut cg, &mut p);
        p.nl();
    }

    generate_main_fn(pgm, main, &mut p);

    p.print()
}

fn forward_declare_fun(fun: &Fun, idx: usize, pgm: &LoweredPgm, p: &mut Printer) {
    w!(p, "// {} {}", loc_display(&fun.name.loc), fun.name.node);
    if !fun.ty_args.is_empty() {
        w!(p, "[");
        for (i, ty_arg) in fun.ty_args.iter().enumerate() {
            if i > 0 {
                w!(p, ", ");
            }
            let mut ty_str = String::new();
            ty_arg.print(&mut ty_str);
            w!(p, "{}", ty_str);
        }
        w!(p, "]");
    }
    p.nl();
    let param_count = fun.params.len();
    w!(p, "static {} _fun_{}(", c_ty(&fun.return_ty, pgm), idx);
    if param_count == 0 {
        w!(p, "void");
    } else {
        for (i, ty) in fun.params.iter().enumerate() {
            if i > 0 {
                w!(p, ", ");
            }
            w!(p, "{} _p{}", c_ty(ty, pgm), i);
        }
    }
    wln!(p, ");");
}

fn forward_declare_closure(closure: &Closure, idx: usize, pgm: &LoweredPgm, p: &mut Printer) {
    wln!(p, "// {}", loc_display(&closure.loc));
    w!(
        p,
        "static {} _closure_{}(CLOSURE* _closure_obj",
        c_ty(&closure.return_ty, pgm),
        idx
    );
    for (i, ty) in closure.params.iter().enumerate() {
        w!(p, ", {} _p{}", c_ty(ty, pgm), i);
    }
    wln!(p, ");");
}

fn gen_closure_struct(closure: &Closure, idx: usize, pgm: &LoweredPgm, p: &mut Printer) {
    if closure.fvs.is_empty() {
        return;
    }

    wln!(p, "// {}", loc_display(&closure.loc));
    w!(p, "typedef struct {{");
    p.indent();
    p.nl();
    wln!(p, "uint64_t tag;");
    wln!(p, "void (*fun)(void);");
    for (i, fv) in closure.fvs.iter().enumerate() {
        if i != 0 {
            p.nl();
        }
        let ty = &closure.locals[fv.use_idx.as_usize()].ty;
        w!(p, "{} _{}; // {}", c_ty(ty, pgm), i, fv.id);
    }
    p.dedent();
    p.nl();
    wln!(p, "}} _Closure_{idx};");
    p.nl();
}

fn heap_obj_to_c(heap_obj: &HeapObj, tag: u32, pgm: &LoweredPgm, p: &mut Printer) {
    match heap_obj {
        HeapObj::Builtin(builtin) => builtin_con_decl_to_c(builtin, tag, pgm, p),
        HeapObj::Source(source_con) => source_con_decl_to_c(source_con, tag, pgm, p),
        HeapObj::Record(record) => record_decl_to_c(record, tag, pgm, p),
        HeapObj::Variant(variant) => variant_decl_to_c(variant, tag, pgm, p),
    }
}

fn builtin_con_decl_to_c(builtin: &BuiltinConDecl, tag: u32, pgm: &LoweredPgm, p: &mut Printer) {
    match builtin {
        BuiltinConDecl::Con | BuiltinConDecl::Fun => {
            // These types are not used in the C backend, instead we generate static `CLOSURE`s.
        }

        BuiltinConDecl::Closure => {
            wln!(p, "#define CLOSURE_TAG {}", tag);
            writedoc!(
                p,
                "
                typedef struct {{
                    uint64_t tag;
                    void (*fun)(void);
                    uint64_t captures[];
                }} CLOSURE;
                "
            );
        }

        BuiltinConDecl::Array { t } => {
            let struct_name = array_struct_name(t, pgm);
            let t = c_ty(t, pgm);
            writedoc!(
                p,
                "
                typedef struct {struct_name} {{
                    uint64_t tag;
                    {t}* data_ptr; // initially points to the the `data` at the end
                    uint64_t len;
                    {t} data[];
                }} {struct_name};
                "
            );
        }

        BuiltinConDecl::I8 => {
            wln!(p, "// I8 tag {}", tag);
            wln!(p, "typedef int8_t I8;");
        }

        BuiltinConDecl::U8 => {
            wln!(p, "// U8 tag {}", tag);
            wln!(p, "typedef uint8_t U8;");
        }

        BuiltinConDecl::I32 => {
            wln!(p, "// I32 tag {}", tag);
            wln!(p, "typedef int32_t I32;");
        }

        BuiltinConDecl::U32 => {
            wln!(p, "// U32 tag {}", tag);
            wln!(p, "typedef uint32_t U32;");
        }

        BuiltinConDecl::I64 => {
            wln!(p, "// I64 tag {}", tag);
            wln!(p, "typedef int64_t I64;");
        }

        BuiltinConDecl::U64 => {
            wln!(p, "// U64 tag {}", tag);
            wln!(p, "typedef uint64_t U64;");
        }
    }
}

fn source_con_tag_name(source_con: &SourceConDecl) -> String {
    let mut tag_name = String::from("TAG_");
    tag_name.push_str(&source_con.name);
    for ty_arg in &source_con.ty_args {
        tag_name.push('_');
        ty_to_c(ty_arg, &mut tag_name);
    }
    tag_name
}

fn source_con_struct_name(source_con: &SourceConDecl) -> String {
    let mut name = source_con.name.to_string();
    for ty_arg in &source_con.ty_args {
        name.push('_');
        ty_to_c(ty_arg, &mut name);
    }
    name
}

fn record_struct_name(record: &RecordType) -> String {
    let mut name = String::from("Record");
    for (field_name, field_ty) in &record.fields {
        name.push('_');
        name.push_str(field_name);
        name.push('_');
        ty_to_c(field_ty, &mut name);
    }
    name
}

fn variant_struct_name(variant: &VariantType) -> String {
    let mut name = String::from("Variant");
    for named_ty in variant.alts.values() {
        name.push('_');
        named_ty_to_c(named_ty, &mut name);
    }
    name
}

fn array_struct_name(t: &mono::Type, pgm: &LoweredPgm) -> String {
    let mut name = String::from("Array_");
    let t = c_ty(t, pgm);
    let t_no_star = t.as_str().strip_suffix("*").unwrap_or(t.as_ref());
    name.push_str(t_no_star);
    name
}

fn heap_obj_struct_name(pgm: &LoweredPgm, idx: HeapObjIdx) -> String {
    match &pgm.heap_objs[idx.0 as usize] {
        HeapObj::Source(source_con) => source_con_struct_name(source_con),
        HeapObj::Record(record) => record_struct_name(record),
        HeapObj::Variant(variant) => variant_struct_name(variant),
        HeapObj::Builtin(_) => panic!("Builtin in heap_obj_struct_name"),
    }
}

fn heap_obj_tag_name(pgm: &LoweredPgm, idx: HeapObjIdx) -> String {
    match &pgm.heap_objs[idx.0 as usize] {
        HeapObj::Source(source_con) => source_con_tag_name(source_con),
        HeapObj::Record(record) => format!("TAG_{}", record_struct_name(record)),
        HeapObj::Variant(_) => panic!("Variants don't have runtime tags"),
        HeapObj::Builtin(_) => panic!("Builtin in heap_obj_tag_name"),
    }
}

fn sum_struct_name(ty_id: &Id, ty_args: &[mono::Type]) -> String {
    let mut struct_name = ty_id.to_string();
    for ty_arg in ty_args {
        struct_name.push('_');
        ty_to_c(ty_arg, &mut struct_name);
    }
    struct_name
}

/// Generate singleton variable name for a nullary source constructor.
fn source_con_singleton_name(source_con: &SourceConDecl) -> String {
    let mut name = String::from("_singleton_");
    name.push_str(&source_con.name);
    for ty_arg in &source_con.ty_args {
        name.push('_');
        ty_to_c(ty_arg, &mut name);
    }
    name
}

/// Get the singleton variable name for a heap object (nullary constructors only).
fn heap_obj_singleton_name(pgm: &LoweredPgm, idx: HeapObjIdx) -> String {
    match &pgm.heap_objs[idx.0 as usize] {
        HeapObj::Source(source_con) => source_con_singleton_name(source_con),
        HeapObj::Record(record) => format!("_singleton_{}", record_struct_name(record)),
        HeapObj::Variant(_) => panic!("Variants don't have singletons"),
        HeapObj::Builtin(_) => panic!("Builtin heap objects don't have singletons"),
    }
}

fn source_con_decl_to_c(source_con: &SourceConDecl, tag: u32, pgm: &LoweredPgm, p: &mut Printer) {
    let SourceConDecl {
        name: _,
        idx,
        ty_args: _,
        fields,
    } = source_con;

    assert_eq!(idx.0, tag);

    let tag_name = source_con_tag_name(source_con);
    let struct_name = source_con_struct_name(source_con);

    wln!(p, "#define {tag_name} {tag}");

    w!(p, "typedef struct {struct_name} {{");
    p.indent();
    p.nl();
    w!(p, "uint64_t _tag;");
    for (i, ty) in fields.iter().enumerate() {
        p.nl();
        w!(p, "{} _{i};", c_ty(ty, pgm));
    }
    p.dedent();
    p.nl();
    wln!(p, "}} {struct_name};");
}

fn record_decl_to_c(record: &RecordType, tag: u32, pgm: &LoweredPgm, p: &mut Printer) {
    let struct_name = record_struct_name(record);

    wln!(p, "#define TAG_{struct_name} {tag}");

    w!(p, "typedef struct {struct_name} {{");
    p.indent();
    p.nl();
    w!(p, "uint64_t _tag;");
    for (i, (_field_name, field_ty)) in record.fields.iter().enumerate() {
        p.nl();
        w!(p, "{} _{i};", c_ty(field_ty, pgm));
    }
    p.dedent();
    p.nl();
    wln!(p, "}} {struct_name};");
}

fn variant_decl_to_c(variant: &VariantType, tag: u32, pgm: &LoweredPgm, p: &mut Printer) {
    let struct_name = variant_struct_name(variant);
    wln!(p, "// tag = {tag}");
    w!(p, "typedef struct {} {{", struct_name);
    p.indent();
    p.nl();
    wln!(p, "uint64_t _tag;");
    w!(p, "union {{");
    p.indent();
    for (i, alt) in variant.alts.values().enumerate() {
        p.nl();
        w!(p, "{} _{i};", c_ty(&mono::Type::Named(alt.clone()), pgm));
    }
    p.dedent();
    p.nl();
    w!(p, "}} _alt;");
    p.dedent();
    p.nl();
    wln!(p, "}} {struct_name};");
}

fn named_ty_to_c(named_ty: &mono::NamedType, out: &mut String) {
    out.push_str(&named_ty.name);
    for arg in &named_ty.args {
        out.push('_');
        ty_to_c(arg, out);
    }
}

fn is_value_type(ty: &mono::Type) -> bool {
    if let mono::Type::Named(mono::NamedType { name, args: _ }) = ty {
        matches!(
            name.as_str(),
            "I8" | "U8" | "I16" | "U16" | "I32" | "U32" | "I64" | "U64"
        )
    } else {
        false
    }
}

fn c_ty(ty: &mono::Type, pgm: &LoweredPgm) -> String {
    if let mono::Type::Named(mono::NamedType { name, args: _ }) = ty {
        let name_str = name.as_str();
        if matches!(
            name_str,
            "I8" | "U8" | "I16" | "U16" | "I32" | "U32" | "I64" | "U64"
        ) {
            return name_str.to_string();
        }
    }
    let value = match ty {
        mono::Type::Named(mono::NamedType { name, args }) => {
            match pgm.type_objs.get(name).unwrap().get(args).unwrap() {
                TypeObjs::Product { value, .. } | TypeObjs::Sum { value, .. } => *value,
            }
        }
        mono::Type::Record { .. } | mono::Type::Variant { .. } => true,
        mono::Type::Fn(_) => return "CLOSURE*".to_string(),
    };
    let mut s = String::new();
    ty_to_c(ty, &mut s);
    if !value {
        s.push('*'); // make pointer
    }
    s
}

fn ty_to_c(ty: &mono::Type, out: &mut String) {
    match ty {
        mono::Type::Named(named_ty) => {
            named_ty_to_c(named_ty, out);
        }

        mono::Type::Record { fields } => {
            out.push_str("Record");
            for (field_name, field_ty) in fields {
                w!(out, "_{}_", field_name);
                ty_to_c(field_ty, out);
            }
        }

        mono::Type::Variant { alts } => {
            out.push_str("Variant");
            for alt in alts.values() {
                out.push('_');
                named_ty_to_c(alt, out);
            }
        }

        mono::Type::Fn(_) => {
            out.push_str("CLOSURE");
        }
    }
}

fn builtin_fun_to_c(
    fun: &BuiltinFunDecl,
    ty_args: &[mono::Type],
    params: &[mono::Type],
    ret: &mono::Type,
    _exn: &mono::Type,
    idx: usize,
    pgm: &LoweredPgm,
    p: &mut Printer,
) {
    // Debug output of `fun` is too noisy, but it's better than not knowing what the generated
    // functions are for.
    wln!(p, "// {:?}", fun);
    match fun {
        BuiltinFunDecl::Panic => {
            writedoc!(
                p,
                "
                static {} _fun_{idx}(Str* msg) {{
                    Array_U8* bytes_arr = msg->_0;
                    uint32_t len = (uint32_t)bytes_arr->len;
                    uint8_t* data_ptr = (uint8_t*)bytes_arr->data_ptr;
                    fprintf(stderr, \"PANIC: \");
                    fwrite(data_ptr, 1, len, stderr);
                    fprintf(stderr, \"\\n\");
                    exit(1);
                }}
                ",
                c_ty(ret, pgm)
            );
        }

        BuiltinFunDecl::PrintStrNoNl => {
            writedoc!(
                p,
                "
                static Record* _fun_{idx}(Str* str) {{
                    Array_U8* bytes_arr = str->_0;
                    uint32_t len = (uint32_t)bytes_arr->len;
                    uint8_t* data_ptr = (uint8_t*)bytes_arr->data_ptr;
                    fwrite(data_ptr, 1, len, stdout);
                    return {};
                }}
                ",
                heap_obj_singleton_name(pgm, pgm.unit_con_idx)
            );
        }

        BuiltinFunDecl::ShrI8 => wln!(p, "static I8 _fun_{idx}(I8 a, I8 b) {{ return a >> b; }}"),

        BuiltinFunDecl::ShrU8 => wln!(p, "static U8 _fun_{idx}(U8 a, U8 b) {{ return a >> b; }}"),

        BuiltinFunDecl::ShrI32 => wln!(
            p,
            "static I32 _fun_{idx}(I32 a, I32 b) {{ return a >> b; }}"
        ),

        BuiltinFunDecl::ShrU32 => wln!(
            p,
            "static U32 _fun_{idx}(U32 a, U32 b) {{ return a >> b; }}"
        ),

        BuiltinFunDecl::BitAndI8 => wln!(p, "static I8 _fun_{idx}(I8 a, I8 b) {{ return a & b; }}"),

        BuiltinFunDecl::BitAndU8 => wln!(p, "static U8 _fun_{idx}(U8 a, U8 b) {{ return a & b; }}"),

        BuiltinFunDecl::BitAndI32 => {
            wln!(p, "static I32 _fun_{idx}(I32 a, I32 b) {{ return a & b; }}")
        }

        BuiltinFunDecl::BitAndU32 => {
            wln!(p, "static U32 _fun_{idx}(U32 a, U32 b) {{ return a & b; }}")
        }

        BuiltinFunDecl::BitOrI8 => wln!(p, "static I8 _fun_{idx}(I8 a, I8 b) {{ return a | b; }}"),

        BuiltinFunDecl::BitOrU8 => wln!(p, "static U8 _fun_{idx}(U8 a, U8 b) {{ return a | b; }}"),

        BuiltinFunDecl::BitOrI32 => {
            wln!(p, "static I32 _fun_{idx}(I32 a, I32 b) {{ return a | b; }}")
        }

        BuiltinFunDecl::BitOrU32 => {
            wln!(p, "static U32 _fun_{idx}(U32 a, U32 b) {{ return a | b; }}")
        }

        BuiltinFunDecl::BitXorU32 => {
            wln!(p, "static U32 _fun_{idx}(U32 a, U32 b) {{ return a ^ b; }}")
        }

        BuiltinFunDecl::ToStrI8 => {
            gen_tostr_fn(idx, "I8", "PRId8", p);
        }

        BuiltinFunDecl::ToStrU8 => {
            gen_tostr_fn(idx, "U8", "PRIu8", p);
        }

        BuiltinFunDecl::ToStrI32 => {
            gen_tostr_fn(idx, "I32", "PRId32", p);
        }

        BuiltinFunDecl::ToStrU32 => {
            gen_tostr_fn(idx, "U32", "PRIu32", p);
        }

        BuiltinFunDecl::ToStrU64 => {
            gen_tostr_fn(idx, "U64", "PRIu64", p);
        }

        BuiltinFunDecl::ToStrI64 => {
            gen_tostr_fn(idx, "I64", "PRId64", p);
        }

        BuiltinFunDecl::U8AsI8 => wln!(p, "static I8 _fun_{idx}(U8 a) {{ return (I8)a; }}"),

        BuiltinFunDecl::U8AsU32 => wln!(p, "static U32 _fun_{idx}(U8 a) {{ return (U32)a; }}"),

        BuiltinFunDecl::U32AsU8 => wln!(p, "static U8 _fun_{idx}(U32 a) {{ return (U8)a; }}"),

        BuiltinFunDecl::U32AsI32 => wln!(p, "static I32 _fun_{idx}(U32 a) {{ return (I32)a; }}"),

        BuiltinFunDecl::U32AsU64 => wln!(p, "static U64 _fun_{idx}(U32 a) {{ return (U64)a; }}"),

        BuiltinFunDecl::I8Shl => wln!(p, "static I8 _fun_{idx}(I8 a, I8 b) {{ return a << b; }}"),

        BuiltinFunDecl::U8Shl => wln!(p, "static U8 _fun_{idx}(U8 a, U8 b) {{ return a << b; }}"),

        BuiltinFunDecl::I32Shl => wln!(
            p,
            "static I32 _fun_{idx}(I32 a, I32 b) {{ return a << b; }}"
        ),

        BuiltinFunDecl::U32Shl => wln!(
            p,
            "static U32 _fun_{idx}(U32 a, U32 b) {{ return a << b; }}"
        ),

        BuiltinFunDecl::I8Cmp => gen_cmp_fn(idx, "I8", pgm, p),
        BuiltinFunDecl::U8Cmp => gen_cmp_fn(idx, "U8", pgm, p),
        BuiltinFunDecl::I32Cmp => gen_cmp_fn(idx, "I32", pgm, p),
        BuiltinFunDecl::U32Cmp => gen_cmp_fn(idx, "U32", pgm, p),
        BuiltinFunDecl::U64Cmp => gen_cmp_fn(idx, "U64", pgm, p),

        BuiltinFunDecl::I8Add => wln!(p, "static I8 _fun_{idx}(I8 a, I8 b) {{ return a + b; }}"),

        BuiltinFunDecl::U8Add => wln!(p, "static U8 _fun_{idx}(U8 a, U8 b) {{ return a + b; }}"),

        BuiltinFunDecl::I32Add => {
            wln!(p, "static I32 _fun_{idx}(I32 a, I32 b) {{ return a + b; }}")
        }

        BuiltinFunDecl::U32Add => {
            wln!(p, "static U32 _fun_{idx}(U32 a, U32 b) {{ return a + b; }}")
        }

        BuiltinFunDecl::U64Add => {
            wln!(p, "static U64 _fun_{idx}(U64 a, U64 b) {{ return a + b; }}")
        }

        BuiltinFunDecl::I8Sub => wln!(p, "static I8 _fun_{idx}(I8 a, I8 b) {{ return a - b; }}"),

        BuiltinFunDecl::U8Sub => wln!(p, "static U8 _fun_{idx}(U8 a, U8 b) {{ return a - b; }}"),

        BuiltinFunDecl::I32Sub => {
            wln!(p, "static I32 _fun_{idx}(I32 a, I32 b) {{ return a - b; }}")
        }

        BuiltinFunDecl::U32Sub => {
            wln!(p, "static U32 _fun_{idx}(U32 a, U32 b) {{ return a - b; }}")
        }

        BuiltinFunDecl::I8Mul => wln!(p, "static I8 _fun_{idx}(I8 a, I8 b) {{ return a * b; }}"),

        BuiltinFunDecl::U8Mul => wln!(p, "static U8 _fun_{idx}(U8 a, U8 b) {{ return a * b; }}"),

        BuiltinFunDecl::I32Mul => {
            wln!(p, "static I32 _fun_{idx}(I32 a, I32 b) {{ return a * b; }}")
        }

        BuiltinFunDecl::U32Mul => {
            wln!(p, "static U32 _fun_{idx}(U32 a, U32 b) {{ return a * b; }}")
        }

        BuiltinFunDecl::U64Mul => {
            wln!(p, "static U64 _fun_{idx}(U64 a, U64 b) {{ return a * b; }}")
        }

        BuiltinFunDecl::I8Div => wln!(p, "static I8 _fun_{idx}(I8 a, I8 b) {{ return a / b; }}"),

        BuiltinFunDecl::U8Div => wln!(p, "static U8 _fun_{idx}(U8 a, U8 b) {{ return a / b; }}"),

        BuiltinFunDecl::I32Div => {
            wln!(p, "static I32 _fun_{idx}(I32 a, I32 b) {{ return a / b; }}")
        }

        BuiltinFunDecl::U32Div => {
            wln!(p, "static U32 _fun_{idx}(U32 a, U32 b) {{ return a / b; }}")
        }

        BuiltinFunDecl::I8Eq
        | BuiltinFunDecl::U8Eq
        | BuiltinFunDecl::I32Eq
        | BuiltinFunDecl::U32Eq => {
            let ty = match fun {
                BuiltinFunDecl::I8Eq => "I8",
                BuiltinFunDecl::U8Eq => "U8",
                BuiltinFunDecl::I32Eq => "I32",
                BuiltinFunDecl::U32Eq => "U32",
                _ => unreachable!(),
            };
            let true_name = heap_obj_singleton_name(pgm, pgm.true_con_idx);
            let false_name = heap_obj_singleton_name(pgm, pgm.false_con_idx);
            wln!(
                p,
                "static Bool* _fun_{idx}({ty} a, {ty} b) {{ return (a == b) ? (Bool*){true_name} : (Bool*){false_name}; }}"
            );
        }

        // TODO: This is rem, not mod.
        BuiltinFunDecl::U32Mod => {
            wln!(p, "static U32 _fun_{idx}(U32 a, U32 b) {{ return a % b; }}")
        }

        BuiltinFunDecl::I8Rem => wln!(p, "static I8 _fun_{idx}(I8 a, I8 b) {{ return a % b; }}"),

        BuiltinFunDecl::U8Rem => wln!(p, "static U8 _fun_{idx}(U8 a, U8 b) {{ return a % b; }}"),

        BuiltinFunDecl::I32Rem => {
            wln!(p, "static I32 _fun_{idx}(I32 a, I32 b) {{ return a % b; }}")
        }

        BuiltinFunDecl::U32Rem => {
            wln!(p, "static U32 _fun_{idx}(U32 a, U32 b) {{ return a % b; }}")
        }

        BuiltinFunDecl::I32AsU32 => wln!(p, "static U32 _fun_{idx}(I32 a) {{ return (U32)a; }}"),

        // TODO: UB, overflows
        BuiltinFunDecl::I32Abs => wln!(
            p,
            "static I32 _fun_{idx}(I32 a) {{ return (v < 0 ? -v : v); }}"
        ),

        // TODO: UB, overflows
        BuiltinFunDecl::I8Neg => wln!(p, "static I8 _fun_{idx}(I8 a) {{ return -a; }}"),

        // TODO: UB, overflows
        BuiltinFunDecl::I32Neg => wln!(p, "static I32 _fun_{idx}(I32 a) {{ return -a; }}"),

        BuiltinFunDecl::ThrowUnchecked => {
            let exn_ty = c_ty(&params[0], pgm);
            w!(
                p,
                "static {} _fun_{}({} exn) {{",
                c_ty(ret, pgm),
                idx,
                exn_ty
            );
            p.indent();
            p.nl();
            wln!(p, "{exn_ty}* boxed = malloc(sizeof({exn_ty}));");
            wln!(p, "*boxed = exn;");
            wln!(p, "throw_exn(boxed);");
            w!(p, "__builtin_unreachable();");
            p.dedent();
            p.nl();
            wln!(p, "}}");
        }

        BuiltinFunDecl::Try { ok_con, err_con } => {
            // prim try(cb: Fn() a / exn) Result[exn, a] / exn?
            // Type args: a, exn, exn? (implicit)
            let cb_ty = match &params[0] {
                mono::Type::Fn(ty) => ty,
                _ => panic!(),
            };
            w!(p, "static {} _fun_{idx}(CLOSURE* cb) {{", c_ty(ret, pgm));
            p.indent();
            p.nl();
            wln!(p, "ExnHandler handler;");
            wln!(p, "handler.prev = current_exn_handler;");
            wln!(p, "current_exn_handler = &handler;");
            w!(p, "if (setjmp(handler.buf) == 0) {{");
            p.indent();
            p.nl();
            wln!(p, "// Call the closure");
            let cb_ret = c_ty(&cb_ty.ret, pgm);
            wln!(
                p,
                "{cb_ret} (*fn)(CLOSURE*) = ({cb_ret} (*)(CLOSURE*))cb->fun;"
            );
            wln!(p, "{cb_ret} result = fn(cb);");
            wln!(p, "current_exn_handler = handler.prev;");
            wln!(p, "// Allocate Ok result");
            let ok_tag_name = heap_obj_tag_name(pgm, *ok_con);
            let ok_struct_name = heap_obj_struct_name(pgm, *ok_con);
            wln!(
                p,
                "{ok_struct_name}* ok = malloc(sizeof({ok_struct_name}));"
            );
            wln!(p, "ok->_tag = {ok_tag_name};");
            wln!(p, "ok->_0 = result;");
            w!(p, "return ({})ok;", c_ty(ret, pgm));
            p.dedent();
            p.nl();
            w!(p, "}} else {{");
            p.indent();
            p.nl();
            wln!(p, "// Exception was thrown");
            let err_tag_name = heap_obj_tag_name(pgm, *err_con);
            let err_struct_name = heap_obj_struct_name(pgm, *err_con);
            wln!(p, "current_exn_handler = handler.prev;");
            wln!(
                p,
                "{err_struct_name}* err = malloc(sizeof({err_struct_name}));"
            );
            wln!(p, "err->_tag = {};", err_tag_name);
            let exn_ty = c_ty(&ty_args[1], pgm);
            wln!(p, "err->_0 = *({exn_ty}*)handler.exn_value;");
            w!(p, "return ({})err;", c_ty(ret, pgm));
            p.dedent();
            p.nl();
            w!(p, "}}");
            p.dedent();
            p.nl();
            wln!(p, "}}");
        }

        // Array functions /////////////////////////////////////////////////////////////////////////
        BuiltinFunDecl::ArrayNew { t, con_idx } => {
            let con_tag = con_idx.as_u64();
            let t_ty = c_ty(t, pgm);
            let mut t_ty_name = String::new();
            ty_to_c(t, &mut t_ty_name);
            let array_ty = c_ty(
                &mono::Type::Named(mono::NamedType {
                    name: Id::new_static("Array"),
                    args: vec![t.clone()],
                }),
                pgm,
            );
            writedoc!(
                p,
                "
                static {array_ty} _fun_{idx}(U32 len) {{
                    size_t data_bytes = (size_t)len * sizeof({t_ty});
                    size_t data_words = (data_bytes + 7) / 8;
                    {array_ty} arr = ({array_ty})malloc(sizeof(Array_{t_ty_name}) + (data_words * sizeof(uint64_t)));
                    arr->tag = {con_tag};
                    arr->data_ptr = ({t_ty}*)(arr + 1);
                    arr->len = len;
                    memset(arr + 1, 0, data_words * sizeof(uint64_t));
                    return arr;
                }}
                "
            );
        }

        BuiltinFunDecl::ArrayLen { t } => {
            let array_ty = c_ty(
                &mono::Type::Named(mono::NamedType {
                    name: Id::new_static("Array"),
                    args: vec![t.clone()],
                }),
                pgm,
            );
            writedoc!(
                p,
                "
                static U32 _fun_{idx}({array_ty} arr) {{
                    return (U32)arr->len;
                }}
                "
            );
        }

        BuiltinFunDecl::ArrayGet { t } => {
            let t_ty = c_ty(t, pgm);
            let array_ty = c_ty(
                &mono::Type::Named(mono::NamedType {
                    name: Id::new_static("Array"),
                    args: vec![t.clone()],
                }),
                pgm,
            );
            writedoc!(
                p,
                "
                static {t_ty} _fun_{idx}({array_ty} arr, U32 idx) {{
                    return arr->data_ptr[idx];
                }}
                "
            );
        }

        BuiltinFunDecl::ArraySet { t } => {
            let t_ty = c_ty(t, pgm);
            let array_ty = c_ty(
                &mono::Type::Named(mono::NamedType {
                    name: Id::new_static("Array"),
                    args: vec![t.clone()],
                }),
                pgm,
            );
            writedoc!(
                p,
                "
                static Record* _fun_{idx}({array_ty} arr, U32 idx, {t_ty} val) {{
                    arr->data_ptr[idx] = val;
                    return {};
                }}
                ",
                heap_obj_singleton_name(pgm, pgm.unit_con_idx)
            );
        }

        BuiltinFunDecl::ArraySlice { t, con_idx } => {
            let con_tag = con_idx.as_u64();
            let t_ty = c_ty(t, pgm);
            let array_struct_name = array_struct_name(t, pgm);
            writedoc!(
                p,
                "
                static {array_struct_name}* _fun_{idx}({array_struct_name}* arr, U32 start, U32 end) {{
                    {array_struct_name}* new_arr = ({array_struct_name}*)malloc(sizeof({array_struct_name}));
                    new_arr->tag = {con_tag};
                    {t_ty}* data_ptr = arr->data_ptr;
                    new_arr->data_ptr = data_ptr + start;
                    new_arr->len = end - start;
                    return new_arr;
                }}
                ",
            );
        }

        BuiltinFunDecl::ArrayCopyWithin { t } => {
            let t_ty = c_ty(t, pgm);
            let array_ty = c_ty(
                &mono::Type::Named(mono::NamedType {
                    name: Id::new_static("Array"),
                    args: vec![t.clone()],
                }),
                pgm,
            );
            writedoc!(
                p,
                "
                static Record* _fun_{idx}({array_ty} arr, U32 src, U32 dst, U32 len) {{
                    {t_ty}* data_ptr = arr->data_ptr;
                    memmove(data_ptr + dst, data_ptr + src, len * sizeof({t_ty}));
                    return {};
                }}
                ",
                heap_obj_singleton_name(pgm, pgm.unit_con_idx)
            );
        }

        // End of array functions //////////////////////////////////////////////////////////////////
        BuiltinFunDecl::ReadFileUtf8 => {
            writedoc!(
                p,
                "
                static Str* _fun_{idx}(Str* path_str) {{
                    Array_U8* bytes_arr = path_str->_0;
                    uint32_t path_len = (uint32_t)bytes_arr->len;
                    uint8_t* path_data = bytes_arr->data_ptr;
                    char* path = (char*)malloc(path_len + 1);
                    memcpy(path, path_data, path_len);
                    path[path_len] = '\\0';
                    FILE* f = fopen(path, \"rb\");
                    free(path);
                    if (!f) {{ fprintf(stderr, \"Failed to open file\\n\"); exit(1); }}
                    fseek(f, 0, SEEK_END);
                    long size = ftell(f);
                    fseek(f, 0, SEEK_SET);
                    char* contents = (char*)malloc(size);
                    if (fread(contents, 1, size, f) != (size_t)size) {{ fprintf(stderr, \"Failed to read file\\n\"); exit(1); }}
                    fclose(f);
                    Str* result = alloc_str(contents, size);
                    free(contents);
                    return result;
                }}
                ",
            );
        }

        BuiltinFunDecl::GetArgs => {
            let array_str_tag = pgm.array_str_con_idx.unwrap().as_u64();
            writedoc!(
                p,
                "
                static Array_Str* _fun_{idx}(void) {{
                    Array_Str* arr = (Array_Str*)malloc(sizeof(Array_Str) + (g_argc * sizeof(Str*)));
                    arr->tag = {array_str_tag};
                    arr->data_ptr = (Str**)(arr + 1);
                    arr->len = g_argc;
                    for (int i = 0; i < g_argc; i++) {{
                        Str* arg_str = alloc_str(g_argv[i], strlen(g_argv[i]));
                        arr->data_ptr[i] = arg_str;
                    }}
                    return arr;
                }}
                ",
            );
        }
    }
}

fn gen_tostr_fn(idx: usize, arg_ty: &str, fmt: &str, p: &mut Printer) {
    w!(p, "static Str* _fun_{}({arg_ty} a) {{", idx);
    p.indent();
    p.nl();
    wln!(p, "char buf[32];");
    w!(p, "int len = snprintf(buf, sizeof(buf), \"%\" {fmt} , a);",);
    p.nl();
    w!(p, "return alloc_str(buf, len);");
    p.dedent();
    p.nl();
    wln!(p, "}}");
}

fn gen_cmp_fn(idx: usize, arg_ty: &str, pgm: &LoweredPgm, p: &mut Printer) {
    w!(p, "static Ordering* _fun_{idx}({arg_ty} a, {arg_ty} b) {{");
    p.indent();
    p.nl();
    w!(
        p,
        "if (a < b) return (Ordering*){};",
        heap_obj_singleton_name(pgm, pgm.ordering_less_con_idx)
    );
    p.nl();
    w!(
        p,
        "if (a > b) return (Ordering*){};",
        heap_obj_singleton_name(pgm, pgm.ordering_greater_con_idx)
    );
    p.nl();
    w!(
        p,
        "return (Ordering*){};",
        heap_obj_singleton_name(pgm, pgm.ordering_equal_con_idx)
    );
    p.dedent();
    p.nl();
    wln!(p, "}}");
}

fn source_fun_to_c(fun: &Fun, source: &SourceFunDecl, idx: usize, cg: &mut Cg, p: &mut Printer) {
    let loc = &fun.name.loc;
    w!(p, "// {} {}", loc_display(loc), fun.name.node);
    if !fun.ty_args.is_empty() {
        w!(p, "[");
        for (i, ty_arg) in fun.ty_args.iter().enumerate() {
            if i > 0 {
                w!(p, ", ");
            }
            let mut ty_str = String::new();
            ty_arg.print(&mut ty_str);
            w!(p, "{}", ty_str);
        }
        w!(p, "]");
    }
    p.nl();
    w!(p, "static {} _fun_{}(", c_ty(&fun.return_ty, cg.pgm), idx);
    for (i, ty) in fun.params.iter().enumerate() {
        if i > 0 {
            w!(p, ", ");
        }
        w!(p, "{} _{}", c_ty(ty, cg.pgm), i);
    }
    w!(p, ") {{");
    p.indent();
    p.nl();

    // Declare locals. First few locals are for parameters, skip those.
    for (i, local) in source.locals.iter().enumerate().skip(fun.params.len()) {
        wln!(
            p,
            "{} _{}; // {}: {}",
            c_ty(&local.ty, cg.pgm),
            i,
            local.name,
            local.ty
        );
    }

    // Declare result variable
    w!(p, "{} _result;", c_ty(&fun.return_ty, cg.pgm));
    p.nl();

    // Generate body
    stmts_to_c(&source.body, Some("_result"), &source.locals, cg, p);

    w!(p, "return _result;");
    p.dedent();
    p.nl();
    wln!(p, "}}");
}

fn closure_to_c(closure: &Closure, idx: usize, cg: &mut Cg, p: &mut Printer) {
    w!(
        p,
        "static {} _closure_{}(CLOSURE* _closure_obj",
        c_ty(&closure.return_ty, cg.pgm),
        idx
    );
    for (i, ty) in closure.params.iter().enumerate() {
        w!(p, ", {} _{}", c_ty(ty, cg.pgm), i);
    }
    w!(p, ") {{");
    p.indent();
    p.nl();

    // Declare locals.
    for (i, local) in closure.locals.iter().enumerate().skip(closure.params.len()) {
        wln!(
            p,
            "{} _{}; // {}: {}",
            c_ty(&local.ty, cg.pgm),
            i,
            local.name,
            local.ty
        );
    }

    // Load free variables from closure object
    if !closure.fvs.is_empty() {
        for (i, fv) in closure.fvs.iter().enumerate() {
            w!(
                p,
                "_{} = ((_Closure_{}*)_closure_obj)->_{}; // {}",
                fv.use_idx.as_usize(),
                idx,
                i,
                fv.id
            );
            p.nl();
        }
    }

    // Declare result variable
    w!(p, "{} _result;", c_ty(&closure.return_ty, cg.pgm));
    p.nl();

    // Generate body
    stmts_to_c(&closure.body, Some("_result"), &closure.locals, cg, p);

    w!(p, "return _result;");
    p.dedent();
    p.nl();
    wln!(p, "}}");
}

fn stmts_to_c(
    stmts: &[mono::L<Stmt>],
    result_var: Option<&str>,
    locals: &[LocalInfo],
    cg: &mut Cg,
    p: &mut Printer,
) {
    if stmts.is_empty() {
        if let Some(result_var) = result_var {
            wln!(
                p,
                "{result_var} = {};",
                heap_obj_singleton_name(cg.pgm, cg.pgm.unit_con_idx)
            );
        }
        return;
    }
    let last_stmt_idx = stmts.len() - 1;
    for (i, stmt) in stmts.iter().enumerate() {
        stmt_to_c(
            &stmt.node,
            &stmt.loc,
            if i == last_stmt_idx { result_var } else { None },
            locals,
            cg,
            p,
        );
    }
}

fn stmt_to_c(
    stmt: &Stmt,
    loc: &Loc,
    result_var: Option<&str>,
    locals: &[LocalInfo],
    cg: &mut Cg,
    p: &mut Printer,
) {
    match stmt {
        Stmt::Let(LetStmt { lhs, rhs, rhs_ty }) => {
            let rhs_temp = cg.fresh_temp();
            w!(p, "{} {} = ", c_ty(rhs_ty, cg.pgm), rhs_temp);
            expr_to_c(&rhs.node, &rhs.loc, locals, cg, p);
            wln!(p, "; // {}", loc_display(&rhs.loc));
            wln!(
                p,
                "{};",
                pat_to_cond(&lhs.node, &rhs_temp, rhs_ty, None, locals, cg)
            );
            if let Some(result_var) = result_var {
                wln!(
                    p,
                    "{result_var} = {};",
                    heap_obj_singleton_name(cg.pgm, cg.pgm.unit_con_idx)
                );
            }
        }

        Stmt::Assign(AssignStmt { lhs, rhs }) => match &lhs.node {
            Expr::LocalVar(idx) => {
                w!(p, "_{} = ", idx.as_usize());
                expr_to_c(&rhs.node, &rhs.loc, locals, cg, p);
                wln!(p, ";");
                if let Some(result_var) = result_var {
                    wln!(
                        p,
                        "{result_var} = {};",
                        heap_obj_singleton_name(cg.pgm, cg.pgm.unit_con_idx)
                    );
                }
            }
            Expr::FieldSel(FieldSelExpr {
                object,
                field: _,
                idx,
                object_ty,
            }) => {
                let obj_temp = cg.fresh_temp();
                w!(p, "{} {} = ", c_ty(object_ty, &cg.pgm), obj_temp);
                expr_to_c(&object.node, &object.loc, locals, cg, p);
                wln!(p, "; // {}", loc_display(&object.loc));
                w!(p, "{}->_{} = ", obj_temp, idx);
                expr_to_c(&rhs.node, &rhs.loc, locals, cg, p);
                wln!(p, ";");
                if let Some(result_var) = result_var {
                    wln!(
                        p,
                        "{result_var} = {};",
                        heap_obj_singleton_name(cg.pgm, cg.pgm.unit_con_idx)
                    );
                }
            }
            _ => {
                // Type checker only accepts variables and fields on the LHS.
                panic!(
                    "{}: BUG: Assign statement with fancy LHS",
                    loc_display(&lhs.loc)
                )
            }
        },

        Stmt::Expr(expr) => {
            if let Some(result_var) = result_var {
                w!(p, "{result_var} = ");
            }
            expr_to_c(expr, loc, locals, cg, p);
            wln!(p, ";");
        }

        Stmt::While(WhileStmt { label, cond, body }) => {
            w!(p, "while (1) {{");
            p.indent();
            p.nl();
            let cond_temp = cg.fresh_temp();
            w!(p, "Bool* {cond_temp} = ");
            expr_to_c(&cond.node, &cond.loc, locals, cg, p);
            wln!(p, ";");
            w!(
                p,
                "if ({} == (Bool*){}) break;",
                cond_temp,
                heap_obj_singleton_name(cg.pgm, cg.pgm.false_con_idx)
            );
            p.nl();
            stmts_to_c(body, None, locals, cg, p);
            if let Some(label) = label {
                w!(p, "_continue_{}:;", label);
            }
            p.dedent();
            p.nl();
            wln!(p, "}}");
            if let Some(label) = label {
                wln!(p, "_break_{}:;", label);
            }
            if let Some(result_var) = result_var {
                wln!(
                    p,
                    "{result_var} = {};",
                    heap_obj_singleton_name(cg.pgm, cg.pgm.unit_con_idx)
                );
            }
        }

        Stmt::Break { label, level: _ } => {
            match label {
                Some(label) => w!(p, "goto _break_{};", label),
                None => w!(p, "break;"),
            }
            p.nl();
        }

        Stmt::Continue { label, level: _ } => {
            match label {
                Some(label) => w!(p, "goto _continue_{};", label),
                None => w!(p, "continue;"),
            }
            p.nl();
        }
    }
}

fn expr_to_c(expr: &Expr, loc: &Loc, locals: &[LocalInfo], cg: &mut Cg, p: &mut Printer) {
    match expr {
        Expr::LocalVar(idx) => {
            w!(p, "_{}", idx.as_usize());
        }

        Expr::Fun(fun_idx) => {
            w!(p, "_fun_closure_{}", fun_idx.as_usize());
        }

        Expr::Con(heap_obj_idx) => {
            w!(p, "_con_closure_{}", heap_obj_idx.0);
        }

        Expr::ConAlloc {
            con_idx,
            args,
            arg_tys,
            ret_ty,
        } => {
            assert_eq!(args.len(), arg_tys.len());
            if args.is_empty() {
                w!(
                    p,
                    "({}){}",
                    c_ty(ret_ty, &cg.pgm),
                    heap_obj_singleton_name(cg.pgm, *con_idx)
                );
            } else {
                let struct_name = heap_obj_struct_name(cg.pgm, *con_idx);
                let tag_name = heap_obj_tag_name(cg.pgm, *con_idx);
                w!(p, "({{");
                p.indent();
                p.nl();
                wln!(p, "{struct_name}* _obj = malloc(sizeof({struct_name}));");
                wln!(p, "_obj->_tag = {tag_name};");
                for (i, arg) in args.iter().enumerate() {
                    w!(p, "_obj->_{i} = ");
                    expr_to_c(&arg.node, &arg.loc, locals, cg, p);
                    wln!(p, ";");
                }
                w!(p, "({})_obj;", c_ty(ret_ty, &cg.pgm));
                p.dedent();
                p.nl();
                w!(p, "}})");
            }
        }

        Expr::FieldSel(FieldSelExpr {
            object,
            field: _,
            idx,
            object_ty: _,
        }) => {
            w!(p, "(");
            expr_to_c(&object.node, &object.loc, locals, cg, p);
            w!(p, ")->_{}", idx);
        }

        Expr::Call(CallExpr { fun, args, fun_ty }) => {
            let arg_tys: Vec<&mono::Type> = match &fun_ty.args {
                mono::FunArgs::Positional(args) => args.iter().collect(),
                mono::FunArgs::Named(args) => args.values().collect(),
            };

            assert_eq!(args.len(), arg_tys.len());

            match &fun.node {
                Expr::Fun(fun_idx) => {
                    // Direct function call
                    w!(p, "_fun_{}(", fun_idx.as_usize());
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            w!(p, ", ");
                        }
                        expr_to_c(&arg.node, &arg.loc, locals, cg, p);
                    }
                    w!(p, ")");
                }
                other => {
                    // Closure call
                    w!(p, "({{");
                    p.indent();
                    p.nl();
                    let fun_temp = cg.fresh_temp();
                    w!(p, "CLOSURE* {} = ", fun_temp);
                    expr_to_c(other, &fun.loc, locals, cg, p);
                    wln!(p, ";");

                    // Closure call - need to pass closure object as first arg
                    w!(p, "{} (*_fn)(CLOSURE*", c_ty(&fun_ty.ret, &cg.pgm));
                    let arg_ty_strs: Vec<String> =
                        arg_tys.iter().map(|ty| c_ty(ty, &cg.pgm)).collect();
                    for arg_ty in arg_ty_strs.iter() {
                        w!(p, ", {arg_ty}");
                    }
                    w!(p, ") = ({} (*)(CLOSURE*", c_ty(&fun_ty.ret, &cg.pgm));
                    for arg_ty in arg_ty_strs.iter() {
                        w!(p, ", {arg_ty}");
                    }
                    wln!(p, "))((CLOSURE*){})->fun;", fun_temp);
                    w!(p, "_fn({}", fun_temp);
                    assert_eq!(args.len(), arg_ty_strs.len());
                    for arg in args.iter() {
                        w!(p, ", ");
                        expr_to_c(&arg.node, &arg.loc, locals, cg, p);
                    }
                    w!(p, ");");
                    p.dedent();
                    p.nl();
                    w!(p, "}})");
                }
            }
        }

        Expr::Int(val) => {
            w!(p, "{}ULL", val);
        }

        Expr::Str(s) => {
            w!(p, "alloc_str(\"");
            for byte in s.bytes() {
                if byte == b'"' || byte == b'\\' || !(32..=126).contains(&byte) {
                    // Use octal escapes as hex escapes doesn't have a digit limit, e.g.
                    // `\xaaaaa...` will consider all those `a`s as digits.
                    w!(p, "\\{:03o}", byte);
                } else {
                    w!(p, "{}", byte as char);
                }
            }
            w!(p, "\", {})", s.len());
        }

        Expr::BoolAnd(left, right) => {
            w!(p, "({{");
            p.indent();
            p.nl();
            w!(p, "Bool* _and_result = ");
            expr_to_c(&left.node, &left.loc, locals, cg, p);
            wln!(p, ";");
            w!(
                p,
                "if (_and_result == (Bool*){}) {{",
                heap_obj_singleton_name(cg.pgm, cg.pgm.true_con_idx)
            );
            p.indent();
            p.nl();
            w!(p, "_and_result = ");
            expr_to_c(&right.node, &right.loc, locals, cg, p);
            w!(p, ";");
            p.dedent();
            p.nl();
            wln!(p, "}}");
            w!(p, "_and_result;");
            p.dedent();
            p.nl();
            w!(p, "}})");
        }

        Expr::BoolOr(left, right) => {
            w!(p, "({{");
            p.indent();
            p.nl();
            w!(p, "Bool* _or_result = ");
            expr_to_c(&left.node, &left.loc, locals, cg, p);
            wln!(p, ";");
            w!(
                p,
                "if (_or_result == (Bool*){}) {{",
                heap_obj_singleton_name(cg.pgm, cg.pgm.false_con_idx)
            );
            p.indent();
            p.nl();
            w!(p, "_or_result = ");
            expr_to_c(&right.node, &right.loc, locals, cg, p);
            w!(p, ";");
            p.dedent();
            p.nl();
            wln!(p, "}}");
            w!(p, "_or_result;");
            p.dedent();
            p.nl();
            w!(p, "}})");
        }

        Expr::Return(expr, ty) => {
            w!(p, "({{");
            p.indent();
            p.nl();
            w!(p, "return ");
            expr_to_c(&expr.node, &expr.loc, locals, cg, p);
            wln!(p, ";");
            if is_value_type(ty) {
                w!(p, "0;");
            } else {
                w!(p, "({})NULL;", c_ty(ty, &cg.pgm));
            }
            p.dedent();
            p.nl();
            w!(p, "}})");
        }

        Expr::Match(MatchExpr {
            scrutinee,
            alts,
            scrut_ty,
            ty,
        }) => {
            // println!("{}: {}", loc_display(loc), ty);

            w!(p, "({{");
            p.indent();
            p.nl();
            let scrut_temp = cg.fresh_temp();
            w!(p, "{} {} = ", c_ty(scrut_ty, &cg.pgm), scrut_temp);
            expr_to_c(&scrutinee.node, &scrutinee.loc, locals, cg, p);
            wln!(p, "; // {}", loc_display(&scrutinee.loc));

            let match_temp = if ty.is_unit() {
                None
            } else {
                let match_temp = cg.fresh_temp();
                wln!(
                    p,
                    "{} {match_temp}; // {}",
                    c_ty(ty, &cg.pgm),
                    loc_display(loc)
                );
                Some(match_temp)
            };

            for (i, alt) in alts.iter().enumerate() {
                if i > 0 {
                    w!(p, " else ");
                }
                // Generate pattern match condition
                let cond = pat_to_cond(&alt.pat.node, &scrut_temp, scrut_ty, None, locals, cg);
                w!(p, "if ({}", cond);

                // Add guard if present
                if let Some(guard) = &alt.guard {
                    w!(p, " && (");
                    expr_to_c(&guard.node, &guard.loc, locals, cg, p);
                    w!(
                        p,
                        " == (Bool*){})",
                        heap_obj_singleton_name(cg.pgm, cg.pgm.true_con_idx)
                    );
                }

                w!(p, ") {{");
                p.indent();
                p.nl();
                // Generate RHS
                stmts_to_c(&alt.rhs, match_temp.as_deref(), locals, cg, p);
                p.dedent();
                p.nl();
                w!(p, "}}");
            }
            w!(p, " else {{");
            p.indent();
            p.nl();
            wln!(p, "fprintf(stderr, \"Non-exhaustive pattern match\\n\");");
            w!(p, "exit(1);");
            p.dedent();
            p.nl();
            wln!(p, "}}");
            match match_temp {
                Some(match_temp) => {
                    w!(p, "{match_temp};");
                }
                None => {
                    w!(
                        p,
                        "{};",
                        heap_obj_singleton_name(cg.pgm, cg.pgm.unit_con_idx)
                    );
                }
            }
            p.dedent();
            p.nl();
            w!(p, "}})");
        }

        Expr::If(IfExpr {
            branches,
            else_branch,
            ty,
        }) => {
            // println!("{}: {}", loc_display(loc), ty);

            w!(p, "({{");
            p.indent();
            p.nl();

            let if_temp = if ty.is_unit() {
                None
            } else {
                let if_temp = cg.fresh_temp();
                wln!(
                    p,
                    "{} {if_temp}; // {}",
                    c_ty(ty, &cg.pgm),
                    loc_display(loc)
                );
                Some(if_temp)
            };

            for (i, (cond, body)) in branches.iter().enumerate() {
                if i > 0 {
                    w!(p, " else ");
                }
                let cond_temp = cg.fresh_temp();
                w!(p, "{{");
                p.indent();
                p.nl();
                w!(p, "Bool* {} = ", cond_temp);
                expr_to_c(&cond.node, &cond.loc, locals, cg, p);
                wln!(p, ";");
                w!(
                    p,
                    "if ({} == (Bool*){}) {{",
                    cond_temp,
                    heap_obj_singleton_name(cg.pgm, cg.pgm.true_con_idx)
                );
                p.indent();
                p.nl();
                stmts_to_c(body, if_temp.as_deref(), locals, cg, p);
                p.dedent();
                p.nl();
                w!(p, "}}");
            }

            match else_branch {
                Some(else_body) => {
                    w!(p, " else {{");
                    p.indent();
                    p.nl();
                    stmts_to_c(else_body, if_temp.as_deref(), locals, cg, p);
                    p.dedent();
                    p.nl();
                    w!(p, "}}");
                }
                None => {
                    p.nl();
                }
            }

            // Close all the blocks we opened for conditions
            for _ in 0..branches.len() {
                p.dedent();
                p.nl();
                w!(p, " }}");
            }
            p.nl();
            match if_temp {
                Some(if_temp) => {
                    w!(p, "{if_temp};");
                }
                None => {
                    w!(
                        p,
                        "{};",
                        heap_obj_singleton_name(cg.pgm, cg.pgm.unit_con_idx)
                    );
                }
            }
            p.dedent();
            p.nl();
            w!(p, "}})");
        }

        Expr::ClosureAlloc(closure_idx) => {
            let closure = &cg.pgm.closures[closure_idx.as_usize()];
            let idx = closure_idx.as_usize();
            w!(p, "({{");
            p.indent();
            p.nl();
            if closure.fvs.is_empty() {
                wln!(p, "CLOSURE* _clos = (CLOSURE*)malloc(sizeof(CLOSURE));");
                wln!(p, "_clos->tag = CLOSURE_TAG;");
                w!(p, "_clos->fun = (void(*)(void))_closure_{};", idx);
                p.nl();
            } else {
                wln!(
                    p,
                    "_Closure_{idx}* _clos = (_Closure_{idx}*)malloc(sizeof(_Closure_{idx}));"
                );
                wln!(p, "_clos->tag = CLOSURE_TAG;");
                w!(p, "_clos->fun = (void(*)(void))_closure_{};", idx);
                p.nl();
                for (i, fv) in closure.fvs.iter().enumerate() {
                    w!(
                        p,
                        "_clos->_{} = _{}; // {}",
                        i,
                        fv.alloc_idx.as_usize(),
                        fv.id
                    );
                    p.nl();
                }
            }
            w!(p, "(CLOSURE*)_clos;");
            p.dedent();
            p.nl();
            w!(p, "}})");
        }

        Expr::Is(IsExpr { expr, pat, expr_ty }) => {
            w!(p, "({{");
            p.indent();
            p.nl();
            let expr_temp = cg.fresh_temp();
            w!(p, "{} {} = ", c_ty(expr_ty, &cg.pgm), expr_temp);
            expr_to_c(&expr.node, &expr.loc, locals, cg, p);
            wln!(p, "; // {}", loc_display(&expr.loc));
            wln!(p, "Bool* _is_result;");
            w!(
                p,
                "if ({}) {{",
                pat_to_cond(&pat.node, &expr_temp, expr_ty, None, locals, cg)
            );
            p.indent();
            p.nl();
            w!(
                p,
                "_is_result = (Bool*){};",
                heap_obj_singleton_name(cg.pgm, cg.pgm.true_con_idx)
            );
            p.dedent();
            p.nl();
            w!(p, "}} else {{");
            p.indent();
            p.nl();
            w!(
                p,
                "_is_result = (Bool*){};",
                heap_obj_singleton_name(cg.pgm, cg.pgm.false_con_idx)
            );
            p.dedent();
            p.nl();
            wln!(p, "}}");
            w!(p, "_is_result;");
            p.dedent();
            p.nl();
            w!(p, "}})");
        }

        Expr::Do(stmts, ty) => {
            w!(p, "({{");
            p.indent();
            p.nl();
            let expr_temp = cg.fresh_temp();
            wln!(
                p,
                "{} {expr_temp}; // {}",
                c_ty(ty, &cg.pgm),
                loc_display(loc)
            );
            stmts_to_c(stmts, Some(&expr_temp), locals, cg, p);
            w!(p, "{expr_temp};");
            p.dedent();
            p.nl();
            w!(p, "}})");
        }

        Expr::Variant {
            expr,
            expr_ty,
            variant_ty,
        } => {
            /*
            ~ <expr>

            ==>

            ({ <expr_ty> temp1 = <expr compilation>;
               uint64_t temp2 = get_tag(temp1);
               <variant_ty> temp3 = { .tag = temp2, .alt._N = temp1 };
               temp3; })

            where:

            - `get_tag` is type-specific tag getter
            - `N` is the index of the named type in the variant type
            */

            w!(p, "({{");
            p.indent();
            p.nl();

            // TODO: Check that variant exprs are named types in an earlier pass.
            let expr_named_ty = match expr_ty {
                mono::Type::Named(named_ty) => named_ty,
                _ => panic!(),
            };

            let alt_idx = variant_ty
                .iter()
                .enumerate()
                .find_map(|(idx, (_, alt_ty))| {
                    if alt_ty == expr_named_ty {
                        Some(idx)
                    } else {
                        None
                    }
                })
                .unwrap();

            let variant_struct_name = variant_struct_name(&VariantType {
                alts: variant_ty.clone(),
            });

            let expr_temp = cg.fresh_temp();
            w!(p, "{} {expr_temp} = ", c_ty(expr_ty, &cg.pgm));
            expr_to_c(&expr.node, &expr.loc, locals, cg, p);
            wln!(p, "; // {}", loc_display(&expr.loc));

            let expr_tag_temp = cg.fresh_temp();
            wln!(
                p,
                "uint32_t {expr_tag_temp} = {};",
                gen_get_tag(cg.pgm, &expr_temp, expr_ty)
            );

            let variant_temp = cg.fresh_temp();
            wln!(
                p,
                "{variant_struct_name} {variant_temp} = {{ ._tag = {expr_tag_temp}, ._alt._{alt_idx} = {expr_temp} }};"
            );
            w!(p, "{variant_temp};");

            p.dedent();
            p.nl();
            w!(p, "}})");
        }
    }
}

/// Given a pattern type inside a variant pattern, find which alternative in the variant it matches.
/// Returns the index of the alternative.
fn find_variant_alt_index(pat_ty: &mono::Type, variant_ty: &OrdMap<Id, mono::NamedType>) -> usize {
    let type_name = match pat_ty {
        mono::Type::Named(named_ty) => named_ty.name.as_str(),
        _ => panic!("Non-named type in variant pattern: {:?}", pat_ty),
    };

    variant_ty
        .iter()
        .enumerate()
        .find_map(|(idx, (name, _))| {
            if name.as_str() == type_name {
                Some(idx)
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("Type {type_name} not found in variant alternatives"))
}

/// Check if we need to convert between two variant types. Returns true if both types are variants
/// and they differ.
fn needs_variant_conversion(from_ty: &mono::Type, to_ty: &mono::Type) -> bool {
    match (from_ty, to_ty) {
        (mono::Type::Variant { alts: from_alts }, mono::Type::Variant { alts: to_alts }) => {
            from_alts != to_alts
        }
        _ => false,
    }
}

/// Generate code to convert a value from one variant type to another: unpack the value from the
/// source variant and repack it into the target variant.
fn gen_variant_conversion(
    scrutinee: &str,
    from_ty: &mono::Type,
    to_ty: &mono::Type,
    cg: &mut Cg,
) -> String {
    let (from_alts, to_alts) = match (from_ty, to_ty) {
        (mono::Type::Variant { alts: from }, mono::Type::Variant { alts: to }) => (from, to),
        _ => panic!("gen_variant_conversion called with non-variant types"),
    };

    let to_variant_ty = VariantType {
        alts: to_alts.clone(),
    };
    let to_struct_name = variant_struct_name(&to_variant_ty);

    // Handle empty target variant - this is an unreachable case at runtime,
    // but we still need to generate valid C code. Just copy the tag.
    if to_alts.is_empty() {
        let temp = cg.fresh_temp();
        return format!(
            "({{ {to_struct_name} {temp}; {temp}._tag = ({scrutinee})._tag; {temp}; }})"
        );
    }

    // Find the mapping from source alternative index to target alternative index.
    // The value's tag tells us which alternative is active in the source.
    // We need to find the corresponding alternative in the target and repack.

    // Generate a compound expression that:
    // 1. Reads the tag from the source
    // 2. Based on the tag, copies the value to the appropriate field in the target

    let temp = cg.fresh_temp();
    let mut cases = String::new();

    for (to_idx, (type_name, named_ty)) in to_alts.iter().enumerate() {
        // Find this type in the source variant
        let (from_idx, _) = from_alts
            .iter()
            .enumerate()
            .find(|(_, (name, _))| *name == type_name)
            .unwrap_or_else(|| {
                panic!(
                    "Type {} not found in source variant during conversion",
                    type_name
                )
            });

        let alt_ty = mono::Type::Named(named_ty.clone());
        let expected_tag = gen_get_tag(cg.pgm, &format!("({scrutinee})._alt._{from_idx}"), &alt_ty);

        if !cases.is_empty() {
            cases.push_str(" else ");
        }
        cases.push_str(&format!(
            "if (({scrutinee})._tag == {expected_tag}) {{ {temp}._tag = {expected_tag}; {temp}._alt._{to_idx} = ({scrutinee})._alt._{from_idx}; }}"
        ));
    }

    // Add a fallback case (should never happen if types are correct)
    cases.push_str(" else { fprintf(stderr, \"Invalid variant conversion\\n\"); exit(1); }");

    format!("({{ {to_struct_name} {temp}; {cases} {temp}; }})")
}

/// Generate a C condition expression for pattern matching.
///
/// - `scrutinee` is the expression being matched against.
///
/// - `scrutinee_ty` is the type of the scrutinee (used for generating tag checks with `gen_get_tag`).
///
/// - `tag_expr` is an optional override for how to get the tag. When `Some`, use that expression
///   directly (e.g., for variant patterns where we check the variant's `_tag` field). When `None`,
///   derive the tag from the scrutinee using `gen_get_tag`.
fn pat_to_cond(
    pat: &Pat,
    scrutinee: &str,
    scrutinee_ty: &mono::Type,
    tag_expr: Option<&str>,
    locals: &[LocalInfo],
    cg: &mut Cg,
) -> String {
    match pat {
        Pat::Ignore => "1".to_string(),

        Pat::Var(VarPat { idx, original_ty }) => {
            let refined_ty = &locals[idx.as_usize()].ty;
            if needs_variant_conversion(original_ty, refined_ty) {
                let conversion = gen_variant_conversion(scrutinee, original_ty, refined_ty, cg);
                format!("({{ _{} = {}; 1; }})", idx.as_usize(), conversion)
            } else {
                format!("({{ _{} = {}; 1; }})", idx.as_usize(), scrutinee)
            }
        }

        Pat::Con(ConPat { con, fields }) => {
            let struct_name = heap_obj_struct_name(cg.pgm, *con);
            let tag_name = heap_obj_tag_name(cg.pgm, *con);
            let tag_check = match tag_expr {
                Some(expr) => format!("({expr} == {tag_name})"),
                None => {
                    let get_tag = gen_get_tag(cg.pgm, scrutinee, scrutinee_ty);
                    format!("({get_tag} == {tag_name})")
                }
            };
            let field_tys: Vec<mono::Type> = match &cg.pgm.heap_objs[con.as_usize()] {
                HeapObj::Source(source_con) => source_con.fields.clone(),
                HeapObj::Record(record) => record.fields.values().cloned().collect(),
                HeapObj::Builtin(_) => panic!("Builtin constructor {:?} in Pat::Con", con),
                HeapObj::Variant(_) => panic!("Variant in Pat::Con"),
            };
            let mut cond = tag_check;
            for (i, field_pat) in fields.iter().enumerate() {
                let field_expr = format!("(({struct_name}*){scrutinee})->_{i}");
                let field_ty = &field_tys[i];
                let field_cond =
                    pat_to_cond(&field_pat.node, &field_expr, field_ty, None, locals, cg);
                cond = format!("({cond} && {field_cond})");
            }
            cond
        }

        Pat::Str(s) => {
            let mut escaped = String::new();
            for byte in s.bytes() {
                if byte == b'"' || byte == b'\\' || !(32..=126).contains(&byte) {
                    escaped.push_str(&format!("\\{:03o}", byte));
                } else {
                    escaped.push(byte as char);
                }
            }
            let tag_check = match tag_expr {
                Some(expr) => format!("({expr} == {})", cg.pgm.str_con_idx.0),
                None => {
                    let get_tag = gen_get_tag(cg.pgm, scrutinee, scrutinee_ty);
                    format!("({get_tag} == {})", cg.pgm.str_con_idx.0)
                }
            };
            format!(
                "({tag_check} && str_eq((Str*){scrutinee}, \"{escaped}\", {}))",
                s.len()
            )
        }

        Pat::Char(c) => {
            let tag_name = heap_obj_tag_name(cg.pgm, cg.pgm.char_con_idx);
            let tag_check = match tag_expr {
                Some(expr) => format!("({expr} == {tag_name})"),
                None => {
                    let get_tag = gen_get_tag(cg.pgm, scrutinee, scrutinee_ty);
                    format!("({get_tag} == {tag_name})")
                }
            };
            format!("({tag_check} && ((Char*){scrutinee})->_0 == {})", *c as u32)
        }

        Pat::Or(p1, p2) => {
            let c1 = pat_to_cond(&p1.node, scrutinee, scrutinee_ty, tag_expr, locals, cg);
            let c2 = pat_to_cond(&p2.node, scrutinee, scrutinee_ty, tag_expr, locals, cg);
            format!("({c1} || {c2})")
        }

        Pat::Variant {
            pat,
            variant_ty,
            pat_ty,
        } => {
            let alt_idx = find_variant_alt_index(pat_ty, variant_ty);
            let inner_expr = format!("({scrutinee})._alt._{alt_idx}");
            let variant_tag_expr = format!("({scrutinee})._tag");
            pat_to_cond(
                &pat.node,
                &inner_expr,
                pat_ty,
                Some(&variant_tag_expr),
                locals,
                cg,
            )
        }
    }
}

fn generate_main_fn(pgm: &LoweredPgm, main: &str, p: &mut Printer) {
    let main_idx = pgm
        .funs
        .iter()
        .enumerate()
        .find_map(|(i, fun)| match &fun.body {
            FunBody::Source(_) if fun.name.node.as_str() == main => Some(i),
            _ => None,
        })
        .unwrap_or_else(|| panic!("Main function {main} is not defined"));

    p.nl();
    w!(p, "int main(int argc, char** argv) {{");
    p.indent();
    p.nl();
    wln!(p, "g_argc = argc;");
    wln!(p, "g_argv = argv;");
    wln!(p, "_fun_{}();", main_idx);
    w!(p, "return 0;");
    p.dedent();
    p.nl();
    wln!(p, "}}");
}

/// Generate the C expression to get the tag of the expression `expr`, which should have the type `ty`.
///
/// For product types: the tag will be the macro that defines the tag.
///
/// For sum types: the tag will be extracted from the expression and the code will depend on whether
/// the sum type is a value type or not.
///
/// - For boxed sum types: the generated code will read the tag word of the heap allocated object.
/// - For unboxed sum types: the generated code will read the tag from the struct of the sum type.
fn gen_get_tag(pgm: &LoweredPgm, expr: &str, ty: &mono::Type) -> String {
    // For product types, use the tag macro.
    match ty {
        mono::Type::Named(mono::NamedType { name, args }) => {
            match pgm.type_objs.get(name).unwrap().get(args).unwrap() {
                TypeObjs::Product { idx, value: _ } => heap_obj_tag_name(pgm, *idx),

                TypeObjs::Sum {
                    con_indices: _,
                    value: true,
                } => {
                    format!("((uint32_t)({expr})._tag)")
                }

                TypeObjs::Sum {
                    con_indices: _,
                    value: false,
                } => {
                    format!("((uint32_t)*(uint64_t*)({expr}))")
                }
            }
        }

        mono::Type::Record { fields } => {
            let heap_obj_idx = *pgm
                .record_objs
                .get(&RecordType {
                    fields: fields.clone(),
                })
                .unwrap();
            heap_obj_tag_name(pgm, heap_obj_idx)
        }

        mono::Type::Variant { alts: _ } => {
            format!("((uint32_t)({expr})._tag)")
        }

        mono::Type::Fn(_) => "CLOSURE_TAG".to_string(),
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Printing utils

#[derive(Debug, Default)]
struct Printer {
    lines: Vec<String>,
    current_line: String,
    indent: u32,
}

impl Printer {
    fn nl(&mut self) {
        let line = std::mem::replace(&mut self.current_line, " ".repeat(self.indent as usize * 4));
        self.lines.push(line)
    }

    fn print(mut self) -> String {
        self.nl();
        let mut out = String::with_capacity(self.lines.iter().map(|l| l.len()).sum());
        for (i, line) in self.lines.iter().enumerate() {
            if i != 0 {
                out.push('\n');
            }
            out.push_str(line);
        }
        out
    }

    fn indent(&mut self) {
        self.indent += 1;
    }

    fn dedent(&mut self) {
        self.indent -= 1;
    }
}

impl Write for Printer {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.current_line.push_str(s);
        Ok(())
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Top sort

/// Topologically sort user-defined types into SCCs.
///
/// - `type_objs`: Maps named types (both products and sums) to their heap object indices.
/// - `record_objs`: Same as `type_objs`, but for records.
fn top_sort(
    type_objs: &HashMap<Id, HashMap<Vec<mono::Type>, TypeObjs>>,
    record_objs: &HashMap<RecordType, HeapObjIdx>,
    variant_objs: &HashMap<VariantType, HeapObjIdx>,
    heap_objs: &[HeapObj],
) -> Vec<HashSet<HeapObjIdx>> {
    let mut idx_gen = SccIdxGen::default();

    let mut output: Vec<HashSet<HeapObjIdx>> = Vec::with_capacity(heap_objs.len());

    // Because the object indices are consecutive numbers from 0 to number of objects, we can use an
    // array to map object indices to things.
    //
    // Assign the first indices to built-ins right away: they can't be analysed and they don't have
    // dependencies, and user-defined types can depend on them. So they need to come first. (I think
    // they may already come first in `heap_objs` so they'll get the first SCC indices, but we don't
    // have to rely on that, we can just give the the first indices here)
    let mut nodes: Box<[SccNode]> = heap_objs
        .iter()
        .enumerate()
        .map(|(heap_obj_idx, heap_obj)| SccNode {
            idx: match heap_obj {
                HeapObj::Builtin(BuiltinConDecl::Array { .. }) => None,
                HeapObj::Builtin(_) => {
                    output.push(std::iter::once(HeapObjIdx(heap_obj_idx as u32)).collect());
                    Some(idx_gen.next())
                }
                HeapObj::Source(_) | HeapObj::Record(_) | HeapObj::Variant(_) => None,
            },
            low_link: None,
            on_stack: false,
        })
        .collect();

    let mut stack: Vec<HeapObjIdx> = Vec::with_capacity(10);

    for (heap_obj_idx, _) in heap_objs.iter().enumerate() {
        if nodes[heap_obj_idx].idx.is_none() {
            _scc(
                type_objs,
                record_objs,
                variant_objs,
                heap_objs,
                HeapObjIdx(heap_obj_idx as u32),
                &mut idx_gen,
                &mut nodes,
                &mut stack,
                &mut output,
            );
        }
    }

    output
}

#[derive(Debug)]
struct SccNode {
    idx: Option<SccIdx>,
    low_link: Option<SccIdx>,
    on_stack: bool,
}

#[derive(Debug, Default)]
struct SccIdxGen {
    next: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct SccIdx(u32);

impl SccIdxGen {
    fn next(&mut self) -> SccIdx {
        let next = self.next;
        self.next += 1;
        SccIdx(next)
    }
}

fn _scc(
    type_objs: &HashMap<Id, HashMap<Vec<mono::Type>, TypeObjs>>,
    record_objs: &HashMap<RecordType, HeapObjIdx>,
    variant_objs: &HashMap<VariantType, HeapObjIdx>,
    heap_objs: &[HeapObj],
    heap_obj_idx: HeapObjIdx,
    idx_gen: &mut SccIdxGen,
    nodes: &mut [SccNode],
    stack: &mut Vec<HeapObjIdx>,
    output: &mut Vec<HashSet<HeapObjIdx>>,
) {
    let idx = idx_gen.next();

    nodes[heap_obj_idx.as_usize()].idx = Some(idx);
    nodes[heap_obj_idx.as_usize()].low_link = Some(idx);
    nodes[heap_obj_idx.as_usize()].on_stack = true;

    stack.push(heap_obj_idx);

    // Add dependencies to the output.
    let deps = heap_obj_deps(
        type_objs,
        record_objs,
        variant_objs,
        heap_objs,
        heap_obj_idx,
    );
    for dep_obj in deps {
        if nodes[dep_obj.as_usize()].idx.is_none() {
            // Dependency not visited yet.
            _scc(
                type_objs,
                record_objs,
                variant_objs,
                heap_objs,
                dep_obj,
                idx_gen,
                nodes,
                stack,
                output,
            );
            let current_low_link = nodes[heap_obj_idx.as_usize()].low_link.unwrap();
            let dep_low_link = nodes[dep_obj.as_usize()].low_link.unwrap();
            nodes[heap_obj_idx.as_usize()].low_link = Some(current_low_link.min(dep_low_link));
        } else if nodes[dep_obj.as_usize()].on_stack {
            // Dependency is on stack, so in the current SCC.
            let current_low_link = nodes[heap_obj_idx.as_usize()].low_link.unwrap();
            let dep_idx = nodes[dep_obj.as_usize()].idx.unwrap();
            nodes[heap_obj_idx.as_usize()].low_link = Some(current_low_link.min(dep_idx));
        }
    }

    // If current node is  aroot node, pop the stack and generate an SCC.
    if nodes[heap_obj_idx.as_usize()].low_link == nodes[heap_obj_idx.as_usize()].idx {
        let mut scc: HashSet<HeapObjIdx> = Default::default();
        loop {
            let dep = stack.pop().unwrap();
            nodes[dep.as_usize()].on_stack = false;
            scc.insert(dep);
            if dep == heap_obj_idx {
                break;
            }
        }

        output.push(scc);
    }
}

fn heap_obj_deps(
    type_objs: &HashMap<Id, HashMap<Vec<mono::Type>, TypeObjs>>,
    record_objs: &HashMap<RecordType, HeapObjIdx>,
    variant_objs: &HashMap<VariantType, HeapObjIdx>,
    heap_objs: &[HeapObj],
    heap_obj_idx: HeapObjIdx,
) -> HashSet<HeapObjIdx> {
    let mut deps: HashSet<HeapObjIdx> = Default::default();

    match &heap_objs[heap_obj_idx.as_usize()] {
        HeapObj::Builtin(BuiltinConDecl::Array { t }) => {
            type_heap_obj_deps(type_objs, record_objs, variant_objs, t, &mut deps);
        }

        HeapObj::Builtin(_) => {}

        HeapObj::Source(source_decl) => {
            for field in source_decl.fields.iter() {
                type_heap_obj_deps(type_objs, record_objs, variant_objs, field, &mut deps);
            }
        }

        HeapObj::Record(record_type) => {
            for field in record_type.fields.values() {
                type_heap_obj_deps(type_objs, record_objs, variant_objs, field, &mut deps);
            }
        }

        HeapObj::Variant(variant_type) => {
            for named_ty in variant_type.alts.values() {
                named_type_heap_obj_deps(type_objs, named_ty, &mut deps);
            }
        }
    }

    deps
}

fn type_heap_obj_deps(
    type_objs: &HashMap<Id, HashMap<Vec<mono::Type>, TypeObjs>>,
    record_objs: &HashMap<RecordType, HeapObjIdx>,
    variant_objs: &HashMap<VariantType, HeapObjIdx>,
    ty: &mono::Type,
    deps: &mut HashSet<HeapObjIdx>,
) {
    match ty {
        mono::Type::Named(ty) => {
            named_type_heap_obj_deps(type_objs, ty, deps);
        }

        mono::Type::Record { fields } => {
            let record_idx = *record_objs
                .get(&RecordType {
                    fields: fields.clone(),
                })
                .unwrap();
            deps.insert(record_idx);
            for ty in fields.values() {
                type_heap_obj_deps(type_objs, record_objs, variant_objs, ty, deps);
            }
        }

        mono::Type::Variant { alts } => {
            let variant_idx = *variant_objs
                .get(&VariantType { alts: alts.clone() })
                .unwrap();
            deps.insert(variant_idx);
            for ty in alts.values() {
                named_type_heap_obj_deps(type_objs, ty, deps);
            }
        }

        mono::Type::Fn(mono::FnType { args, ret, exn }) => {
            match args {
                mono::FunArgs::Positional(args) => {
                    for arg in args {
                        type_heap_obj_deps(type_objs, record_objs, variant_objs, arg, deps);
                    }
                }
                mono::FunArgs::Named(args) => {
                    for arg in args.values() {
                        type_heap_obj_deps(type_objs, record_objs, variant_objs, arg, deps);
                    }
                }
            }

            type_heap_obj_deps(type_objs, record_objs, variant_objs, ret, deps);
            type_heap_obj_deps(type_objs, record_objs, variant_objs, exn, deps);
        }
    }
}

fn named_type_heap_obj_deps(
    type_objs: &HashMap<Id, HashMap<Vec<mono::Type>, TypeObjs>>,
    ty: &mono::NamedType,
    deps: &mut HashSet<HeapObjIdx>,
) {
    let ty_map = match type_objs.get(&ty.name) {
        Some(ty_map) => ty_map,
        None => return, // builtin
    };

    match ty_map.get(&ty.args).unwrap() {
        TypeObjs::Product { idx, value: _ } => {
            deps.insert(*idx);
        }
        TypeObjs::Sum {
            con_indices,
            value: _,
        } => deps.extend(con_indices.iter().cloned()),
    }
}
