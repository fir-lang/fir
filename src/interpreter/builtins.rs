use crate::ast::Loc;
use crate::interpreter::*;
use crate::utils::loc_display;

use std::io::Write;

use bytemuck::cast_slice;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinFun {
    // Top funs
    Panic,
    Print,
    PrintStr,

    // Assoc funs
    ArrayI8Get,
    ArrayI8Len,
    ArrayI8New,
    ArrayI8Set,

    ArrayU8Get,
    ArrayU8Len,
    ArrayU8New,
    ArrayU8Set,

    ArrayI32Get,
    ArrayI32Len,
    ArrayI32New,
    ArrayI32Set,

    ArrayU32Get,
    ArrayU32Len,
    ArrayU32New,
    ArrayU32Set,

    ArrayPtrGet,
    ArrayPtrLen,
    ArrayPtrNew,
    ArrayPtrSet,

    // I32
    I32Add,
    I32Cmp,
    I32Eq,
    I32Mul,
    I32Div,
    I32Sub,
    I32ToStr,
    I32BitOr,
    I32BitAnd,
    I32Shl,
    I32Shr,
    I32AsI8,
    I32AsU8,
    I32AsU32,

    // U32
    U32Add,
    U32Cmp,
    U32Eq,
    U32Mul,
    U32Div,
    U32Sub,
    U32ToStr,
    U32BitOr,
    U32BitAnd,
    U32Shl,
    U32Shr,
    U32AsI8,
    U32AsU8,
    U32AsI32,

    // I8
    I8Add,
    I8Cmp,
    I8Eq,
    I8Mul,
    I8Div,
    I8Sub,
    I8ToStr,
    I8BitOr,
    I8BitAnd,
    I8Shl,
    I8Shr,
    I8AsU8,
    I8AsI32,
    I8AsU32,

    // U8
    U8Add,
    U8Cmp,
    U8Eq,
    U8Mul,
    U8Div,
    U8Sub,
    U8ToStr,
    U8BitOr,
    U8BitAnd,
    U8Shl,
    U8Shr,
    U8AsI8,
    U8AsI32,
    U8AsU32,

    // Exception handling
    Try,
    TryU32,
    Throw,

    ReadFileUtf8,
}

macro_rules! array_new {
    ($pgm:expr, $heap:expr, $args:expr, $array_type_tag:expr, $elem_size_in_bytes:expr) => {{
        debug_assert_eq!($args.len(), 1);
        let cap = $args[0];
        let cap_words = (cap * $elem_size_in_bytes).div_ceil(8);
        let array = $heap.allocate(cap_words as usize + 2);
        $heap[array] = $array_type_tag;
        $heap[array + 1] = cap as u64;
        (&mut $heap.values[(array + 2) as usize..(array + 2 + cap_words) as usize]).fill(0);
        array
    }};
}

macro_rules! array_set {
    ($pgm:expr, $heap:expr, $args:expr, $array_type_tag:expr, $elem_rust_type:ty, $val_to_elem:expr) => {{
        debug_assert_eq!($args.len(), 3);

        let array = $args[0];
        debug_assert_eq!($heap[array], $array_type_tag);

        let idx = $args[1];
        let elem = $val_to_elem($args[2]);

        let array_len = $heap[array + 1];
        if idx >= array_len {
            panic!("OOB array access (idx = {}, len = {})", idx, array_len);
        }

        let payload: &mut [$elem_rust_type] =
            cast_slice_mut(&mut $heap.values[array as usize + 2..]);
        payload[idx as usize] = elem;
        0
    }};
}

macro_rules! array_get {
    ($pgm:expr, $heap:expr, $args:expr, $array_type_tag:expr, $elem_rust_type:ty, $elem_as_val:expr) => {{
        debug_assert_eq!($args.len(), 2);

        let array = $args[0];
        debug_assert_eq!($heap[array], $array_type_tag);

        let idx = $args[1];

        let array_len = $heap[array + 1];
        if idx >= array_len {
            panic!("OOB array access (idx = {}, len = {})", idx, array_len);
        }

        let payload: &[$elem_rust_type] = cast_slice(&$heap.values[array as usize + 2..]);
        $elem_as_val(payload[idx as usize])
    }};
}

pub fn call_builtin_fun<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    fun: &BuiltinFun,
    args: Vec<u64>,
    loc: &Loc,
) -> FunRet {
    let val = match fun {
        BuiltinFun::Panic => {
            debug_assert!(args.len() <= 1);

            let msg: String = if args.len() == 1 {
                let msg = args[0];
                let bytes = heap.str_bytes(msg);
                String::from_utf8_lossy(bytes).into_owned()
            } else {
                "".to_string()
            };

            panic!("{}: PANIC: {}", loc_display(loc), msg);
        }

        BuiltinFun::Print => {
            debug_assert_eq!(args.len(), 1);
            let obj = args[0];
            let str = obj_to_string(pgm, heap, obj, loc);
            writeln!(w, "{}", str).unwrap();
            0
        }

        BuiltinFun::PrintStr => {
            debug_assert_eq!(args.len(), 1);
            let str = args[0];
            debug_assert_eq!(heap[str], pgm.str_ty_tag);
            let bytes = heap.str_bytes(str);
            writeln!(w, "{}", String::from_utf8_lossy(bytes)).unwrap();
            0
        }

        BuiltinFun::ArrayI8New => {
            array_new!(pgm, heap, args, pgm.array_i8_ty_tag, 1)
        }

        BuiltinFun::ArrayU8New => {
            array_new!(pgm, heap, args, pgm.array_u8_ty_tag, 1)
        }

        BuiltinFun::ArrayI32New => {
            array_new!(pgm, heap, args, pgm.array_i32_ty_tag, 4)
        }

        BuiltinFun::ArrayU32New => {
            array_new!(pgm, heap, args, pgm.array_u32_ty_tag, 4)
        }

        BuiltinFun::ArrayPtrNew => {
            array_new!(pgm, heap, args, pgm.array_ptr_ty_tag, 8)
        }

        BuiltinFun::ArrayI8Len
        | BuiltinFun::ArrayU8Len
        | BuiltinFun::ArrayI32Len
        | BuiltinFun::ArrayU32Len
        | BuiltinFun::ArrayPtrLen => {
            debug_assert_eq!(args.len(), 1);
            let array = args[0];
            heap[array + 1]
        }

        BuiltinFun::ArrayI8Set => {
            array_set!(pgm, heap, args, pgm.array_i8_ty_tag, i8, val_as_i8)
        }

        BuiltinFun::ArrayU8Set => {
            array_set!(pgm, heap, args, pgm.array_u8_ty_tag, u8, val_as_u8)
        }

        BuiltinFun::ArrayI32Set => {
            array_set!(pgm, heap, args, pgm.array_i32_ty_tag, i32, val_as_i32)
        }

        BuiltinFun::ArrayU32Set => {
            array_set!(pgm, heap, args, pgm.array_u32_ty_tag, u32, val_as_u32)
        }

        BuiltinFun::ArrayPtrSet => {
            array_set!(pgm, heap, args, pgm.array_ptr_ty_tag, u64, |val| val)
        }

        BuiltinFun::ArrayI8Get => {
            array_get!(pgm, heap, args, pgm.array_i8_ty_tag, i8, i8_as_val)
        }

        BuiltinFun::ArrayU8Get => {
            array_get!(pgm, heap, args, pgm.array_u8_ty_tag, u8, u8_as_val)
        }

        BuiltinFun::ArrayI32Get => {
            array_get!(pgm, heap, args, pgm.array_i32_ty_tag, i32, i32_as_val)
        }

        BuiltinFun::ArrayU32Get => {
            array_get!(pgm, heap, args, pgm.array_u32_ty_tag, u32, u32_as_val)
        }

        BuiltinFun::ArrayPtrGet => {
            array_get!(pgm, heap, args, pgm.array_ptr_ty_tag, u64, |val| val)
        }

        BuiltinFun::I32Add => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            i32_as_val(val_as_i32(i1) + val_as_i32(i2))
        }

        BuiltinFun::I32Sub => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            i32_as_val(val_as_i32(i1) - val_as_i32(i2))
        }

        BuiltinFun::I32Mul => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            i32_as_val(val_as_i32(i1) * val_as_i32(i2))
        }

        BuiltinFun::I32Div => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            i32_as_val(val_as_i32(i1) / val_as_i32(i2))
        }

        BuiltinFun::I32Cmp => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            let ordering_ty_con = pgm.ty_cons.get("Ordering").unwrap_or_else(|| {
                panic!("__cmp was called, but the Ordering type is not defined")
            });

            let constr_name = match i1.cmp(&i2) {
                Ordering::Less => "Less",
                Ordering::Equal => "Equal",
                Ordering::Greater => "Greater",
            };

            heap.allocate_tag(ordering_ty_con.get_constr_with_tag(constr_name).0)
        }

        BuiltinFun::I32Eq => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            pgm.bool_alloc(i1 == i2)
        }

        BuiltinFun::I32BitOr => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            i32_as_val(val_as_i32(i1) | val_as_i32(i2))
        }

        BuiltinFun::I32BitAnd => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];

            i32_as_val(val_as_i32(i1) & val_as_i32(i2))
        }

        BuiltinFun::I32ToStr => {
            debug_assert_eq!(args.len(), 1);
            let i = args[0];
            heap.allocate_str(
                pgm.str_ty_tag,
                pgm.array_u8_ty_tag,
                format!("{}", i as i32).as_bytes(),
            )
        }

        BuiltinFun::U32Add => {
            debug_assert_eq!(args.len(), 2);

            let u1 = args[0];
            let u2 = args[1];

            u32_as_val(val_as_u32(u1) + val_as_u32(u2))
        }

        BuiltinFun::U32Sub => {
            debug_assert_eq!(args.len(), 2);

            let u1 = args[0];
            let u2 = args[1];

            u32_as_val(val_as_u32(u1) - val_as_u32(u2))
        }

        BuiltinFun::U32Mul => {
            debug_assert_eq!(args.len(), 2);

            let u1 = args[0];
            let u2 = args[1];

            u32_as_val(val_as_u32(u1) * val_as_u32(u2))
        }

        BuiltinFun::U32Div => {
            debug_assert_eq!(args.len(), 2);

            let u1 = args[0];
            let u2 = args[1];

            u32_as_val(val_as_u32(u1) / val_as_u32(u2))
        }

        BuiltinFun::U32Cmp => {
            debug_assert_eq!(args.len(), 2);

            let u1 = args[0];
            let u2 = args[1];

            let ordering_ty_con = pgm.ty_cons.get("Ordering").unwrap_or_else(|| {
                panic!("__cmp was called, but the Ordering type is not defined")
            });

            let constr_name = match (u1 as u32).cmp(&(u2 as u32)) {
                Ordering::Less => "Less",
                Ordering::Equal => "Equal",
                Ordering::Greater => "Greater",
            };

            heap.allocate_tag(ordering_ty_con.get_constr_with_tag(constr_name).0)
        }

        BuiltinFun::U32Eq => {
            debug_assert_eq!(args.len(), 2);

            let u1 = args[0];
            let u2 = args[1];

            pgm.bool_alloc(u1 == u2)
        }

        BuiltinFun::U32BitOr => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            u32_as_val(val_as_u32(i1) | val_as_u32(i2))
        }

        BuiltinFun::U32BitAnd => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            u32_as_val(val_as_u32(i1) & val_as_u32(i2))
        }

        BuiltinFun::U32ToStr => {
            debug_assert_eq!(args.len(), 1);
            let u = args[0];
            heap.allocate_str(
                pgm.str_ty_tag,
                pgm.array_u8_ty_tag,
                format!("{}", u as u32).as_bytes(),
            )
        }

        BuiltinFun::I8Add => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            i8_as_val(val_as_i8(i1) + val_as_i8(i2))
        }

        BuiltinFun::I8Sub => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            i8_as_val(val_as_i8(i1) - val_as_i8(i2))
        }

        BuiltinFun::I8Mul => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            i8_as_val(val_as_i8(i1) * val_as_i8(i2))
        }

        BuiltinFun::I8Div => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            i8_as_val(val_as_i8(i1) / val_as_i8(i2))
        }

        BuiltinFun::I8Cmp => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            let ordering_ty_con = pgm.ty_cons.get("Ordering").unwrap_or_else(|| {
                panic!("__cmp was called, but the Ordering type is not defined")
            });

            let constr_name = match (i1 as i8).cmp(&(i2 as i8)) {
                Ordering::Less => "Less",
                Ordering::Equal => "Equal",
                Ordering::Greater => "Greater",
            };

            heap.allocate_tag(ordering_ty_con.get_constr_with_tag(constr_name).0)
        }

        BuiltinFun::I8Eq => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            pgm.bool_alloc(i1 == i2)
        }

        BuiltinFun::I8BitOr => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            i8_as_val(val_as_i8(i1) | val_as_i8(i2))
        }

        BuiltinFun::I8BitAnd => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];

            i8_as_val(val_as_i8(i1) & val_as_i8(i2))
        }

        BuiltinFun::I8ToStr => {
            debug_assert_eq!(args.len(), 1);
            let i = args[0];
            heap.allocate_str(
                pgm.str_ty_tag,
                pgm.array_u8_ty_tag,
                format!("{}", i as i8).as_bytes(),
            )
        }

        BuiltinFun::U8Add => {
            debug_assert_eq!(args.len(), 2);

            let u1 = args[0];
            let u2 = args[1];

            u8_as_val(val_as_u8(u1) + val_as_u8(u2))
        }

        BuiltinFun::U8Sub => {
            debug_assert_eq!(args.len(), 2);

            let u1 = args[0];
            let u2 = args[1];

            u8_as_val(val_as_u8(u1) - val_as_u8(u2))
        }

        BuiltinFun::U8Mul => {
            debug_assert_eq!(args.len(), 2);

            let u1 = args[0];
            let u2 = args[1];

            u8_as_val(val_as_u8(u1) * val_as_u8(u2))
        }

        BuiltinFun::U8Div => {
            debug_assert_eq!(args.len(), 2);

            let u1 = args[0];
            let u2 = args[1];

            u8_as_val(val_as_u8(u1) / val_as_u8(u2))
        }

        BuiltinFun::U8Cmp => {
            debug_assert_eq!(args.len(), 2);

            let u1 = args[0];
            let u2 = args[1];

            let ordering_ty_con = pgm.ty_cons.get("Ordering").unwrap_or_else(|| {
                panic!("__cmp was called, but the Ordering type is not defined")
            });

            let constr_name = match (u1 as u8).cmp(&(u2 as u8)) {
                Ordering::Less => "Less",
                Ordering::Equal => "Equal",
                Ordering::Greater => "Greater",
            };

            heap.allocate_tag(ordering_ty_con.get_constr_with_tag(constr_name).0)
        }

        BuiltinFun::U8Eq => {
            debug_assert_eq!(args.len(), 2);

            let u1 = args[0];
            let u2 = args[1];

            pgm.bool_alloc(u1 == u2)
        }

        BuiltinFun::U8BitOr => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            u8_as_val(val_as_u8(i1) | val_as_u8(i2))
        }

        BuiltinFun::U8BitAnd => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];

            u8_as_val(val_as_u8(i1) & val_as_u8(i2))
        }

        BuiltinFun::U8ToStr => {
            debug_assert_eq!(args.len(), 1);
            let u = args[0];
            heap.allocate_str(
                pgm.str_ty_tag,
                pgm.array_u8_ty_tag,
                format!("{}", u as u8).as_bytes(),
            )
        }

        BuiltinFun::I32Shl => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            i32_as_val(val_as_i32(i1) << val_as_i32(i2))
        }

        BuiltinFun::I32Shr => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            i32_as_val(val_as_i32(i1) >> val_as_i32(i2))
        }

        BuiltinFun::U32Shl => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            u32_as_val(val_as_u32(i1) << val_as_u32(i2))
        }

        BuiltinFun::U32Shr => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            u32_as_val(val_as_u32(i1) >> val_as_u32(i2))
        }

        BuiltinFun::I8Shl => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            i8_as_val(val_as_i8(i1) << val_as_i8(i2))
        }

        BuiltinFun::I8Shr => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            i8_as_val(val_as_i8(i1) >> val_as_i8(i2))
        }

        BuiltinFun::U8Shl => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            u8_as_val(val_as_u8(i1) << val_as_u8(i2))
        }

        BuiltinFun::U8Shr => {
            debug_assert_eq!(args.len(), 2);
            let i1 = args[0];
            let i2 = args[1];
            u8_as_val(val_as_u8(i1) >> val_as_u8(i2))
        }

        BuiltinFun::I32AsI8 => i8_as_val(val_as_i32(args[0]) as i8),

        BuiltinFun::I32AsU8 => u8_as_val(val_as_i32(args[0]) as u8),

        BuiltinFun::I32AsU32 => args[0],

        BuiltinFun::U32AsI8 => i8_as_val(val_as_u32(args[0]) as i8),

        BuiltinFun::U32AsU8 => u8_as_val(val_as_u32(args[0]) as u8),

        BuiltinFun::U32AsI32 => args[0],

        BuiltinFun::I8AsU8 => args[0],

        BuiltinFun::I8AsI32 => i32_as_val(val_as_i8(args[0]) as i32),

        BuiltinFun::I8AsU32 => u32_as_val(val_as_i8(args[0]) as u32),

        BuiltinFun::U8AsI8 => args[0],

        BuiltinFun::U8AsI32 => i32_as_val(val_as_u8(args[0]) as i32),

        BuiltinFun::U8AsU32 => u32_as_val(val_as_u8(args[0]) as u32),

        BuiltinFun::Try => {
            return try_(w, pgm, heap, args, loc, "Ptr");
        }

        BuiltinFun::TryU32 => {
            return try_(w, pgm, heap, args, loc, "U32");
        }

        BuiltinFun::Throw => {
            debug_assert_eq!(args.len(), 1);
            let exn = args[0];
            return FunRet::Unwind(exn);
        }

        BuiltinFun::ReadFileUtf8 => {
            debug_assert_eq!(args.len(), 1);
            let file_path = args[0];
            debug_assert_eq!(heap[file_path], pgm.str_ty_tag);
            let file_path_bytes = heap.str_bytes(file_path);
            let file_path_str = std::str::from_utf8(file_path_bytes).unwrap();
            let contents = std::fs::read_to_string(file_path_str).unwrap();
            heap.allocate_str(pgm.str_ty_tag, pgm.array_u8_ty_tag, contents.as_bytes())
        }
    };

    FunRet::Val(val)
}

fn try_<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    args: Vec<u64>,
    loc: &Loc,
    val_ty: &str,
) -> FunRet {
    debug_assert_eq!(args.len(), 1);
    let cb = args[0];
    match call_closure(w, pgm, heap, &mut Default::default(), cb, &[], loc) {
        ControlFlow::Val(val) => {
            let ty_con = pgm
                .ty_cons
                .get(("Result@Ptr@".to_owned() + val_ty).as_str())
                .unwrap();

            let constr_idx = ty_con
                .value_constrs
                .iter()
                .enumerate()
                .find(|(_, constr)| constr.name.as_ref() == Some(&SmolStr::new_static("Ok")))
                .unwrap();

            let object = heap.allocate(1 + args.len());
            heap[object] = ty_con.type_tag + constr_idx.0 as u64;
            heap[object + 1] = val;
            FunRet::Val(object)
        }
        ControlFlow::Unwind(val) => {
            let ty_con = pgm
                .ty_cons
                .get(("Result@Ptr@".to_owned() + val_ty).as_str())
                .unwrap();

            let constr_idx = ty_con
                .value_constrs
                .iter()
                .enumerate()
                .find(|(_, constr)| constr.name.as_ref() == Some(&SmolStr::new_static("Err")))
                .unwrap();

            let object = heap.allocate(1 + args.len());
            heap[object] = ty_con.type_tag + constr_idx.0 as u64;
            heap[object + 1] = val;
            FunRet::Val(object)
        }
        ControlFlow::Break | ControlFlow::Continue | ControlFlow::Ret(_) => panic!(),
    }
}
