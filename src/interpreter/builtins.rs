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
    PrintStrView,

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
    I32Sub,
    I32ToStr,
    I32BitOr,
    I32BitAnd,

    // U32
    U32Add,
    U32Cmp,
    U32Eq,
    U32Mul,
    U32Sub,
    U32ToStr,
    U32BitOr,
    U32BitAnd,

    // I8
    I8Add,
    I8Cmp,
    I8Eq,
    I8Mul,
    I8Sub,
    I8ToStr,
    I8BitOr,
    I8BitAnd,

    // U8
    U8Add,
    U8Cmp,
    U8Eq,
    U8Mul,
    U8Sub,
    U8ToStr,
    U8BitOr,
    U8BitAnd,

    StrEq,
    StrLen,
    StrSubstr,
    StrViewEq,
    StrViewIsEmpty,
    StrViewLen,
    StrViewStartsWith,
    StrViewSubstr,
    StrViewToStr,
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
            panic!("OOB array access");
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
            panic!("OOB array access");
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
) -> u64 {
    match fun {
        BuiltinFun::Panic => {
            debug_assert!(args.len() <= 1);

            let msg: String = if args.len() == 1 {
                let msg = args[0];
                let len_bytes = heap[msg + 1];
                let len_words = len_bytes.div_ceil(8);
                let words =
                    &heap.values[(msg as usize) + 2..(msg as usize) + 2 + (len_words as usize)];
                let bytes = cast_slice(words);
                String::from_utf8_lossy(&bytes[..len_bytes as usize]).into_owned()
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

            let len_bytes = heap[str + 1];
            let len_words = len_bytes.div_ceil(8);
            let words = &heap.values[(str as usize) + 2..(str as usize) + 2 + (len_words as usize)];
            let bytes = cast_slice(words);
            writeln!(
                w,
                "{}",
                String::from_utf8_lossy(&bytes[..len_bytes as usize])
            )
            .unwrap();
            0
        }

        BuiltinFun::PrintStrView => {
            debug_assert_eq!(args.len(), 1);
            let str = args[0];
            debug_assert_eq!(heap[str], pgm.str_ty_tag);

            let view_start = heap[str + 1];
            let view_end = heap[str + 2];

            let payload_byte_addr = {
                let viewed_str = heap[str + 3];
                let skip_tag_and_len = viewed_str + 2;
                skip_tag_and_len * 8
            };

            let heap_bytes: &[u8] = cast_slice(&heap.values);
            writeln!(
                w,
                "{}",
                String::from_utf8_lossy(
                    &heap_bytes[(payload_byte_addr + view_start) as usize
                        ..(payload_byte_addr + view_end) as usize]
                )
            )
            .unwrap();

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

        BuiltinFun::StrLen => {
            debug_assert_eq!(args.len(), 1);
            let str = args[0];
            debug_assert_eq!(heap[str], pgm.str_ty_tag);
            heap[str + 1]
        }

        BuiltinFun::StrEq => {
            debug_assert_eq!(args.len(), 2);

            let str1 = args[0];
            let str2 = args[1];

            debug_assert_eq!(heap[str1], pgm.str_ty_tag);
            debug_assert_eq!(heap[str2], pgm.str_ty_tag);

            let str1_len = heap[str1 + 1];
            let str2_len = heap[str2 + 1];

            if str1_len != str2_len {
                return pgm.bool_alloc(false);
            }

            let len_words = str1_len.div_ceil(8);

            for i in 0..len_words {
                if heap[str1 + 2 + i] != heap[str2 + 2 + i] {
                    return pgm.bool_alloc(false);
                }
            }

            pgm.bool_alloc(true)
        }

        BuiltinFun::StrSubstr => {
            debug_assert_eq!(args.len(), 3);

            // Returns a `StrView`.
            let str = args[0];
            let byte_start = args[1];
            let byte_end = args[2];

            debug_assert_eq!(heap[str], pgm.str_ty_tag);

            let str_len = heap[str + 1];

            if byte_start > str_len {
                panic!("String.substr start index out of bounds");
            }

            if byte_end > str_len {
                panic!("String.substr end index out of bounds");
            }

            if byte_start > byte_end {
                panic!("String.substr start index larger than end index");
            }

            heap.allocate_str_view(pgm.str_view_ty_tag, str, byte_start, byte_end)
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
            heap.allocate_str(pgm.str_ty_tag, format!("{}", i as i32).as_bytes())
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
            heap.allocate_str(pgm.str_ty_tag, format!("{}", u as u32).as_bytes())
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
            heap.allocate_str(pgm.str_ty_tag, format!("{}", i as i8).as_bytes())
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
            heap.allocate_str(pgm.str_ty_tag, format!("{}", u as u8).as_bytes())
        }

        BuiltinFun::StrViewEq => {
            debug_assert_eq!(args.len(), 2);

            let s1 = args[0];
            let s2 = args[1];

            debug_assert_eq!(heap[s1], pgm.str_view_ty_tag, "{:?}", loc);
            debug_assert_eq!(heap[s2], pgm.str_view_ty_tag, "{:?}", loc);

            let s1_start = heap[s1 + 1];
            let s1_end = heap[s1 + 2];

            let s2_start = heap[s2 + 1];
            let s2_end = heap[s2 + 2];

            if s1_end - s1_start != s2_end - s2_start {
                return pgm.bool_alloc(false);
            }

            let s1_payload_byte_addr = {
                let viewed_str = heap[s1 + 3];
                let skip_tag_and_len = viewed_str + 2;
                skip_tag_and_len * 8
            };

            let s2_payload_byte_addr = (heap[s2 + 3] + 2) * 8;

            let heap_bytes: &[u8] = cast_slice(&heap.values);

            let eq = heap_bytes[(s1_payload_byte_addr + s1_start) as usize
                ..(s1_payload_byte_addr + s1_end) as usize]
                == heap_bytes[(s2_payload_byte_addr + s2_start) as usize
                    ..(s2_payload_byte_addr + s2_end) as usize];

            pgm.bool_alloc(eq)
        }

        BuiltinFun::StrViewSubstr => {
            debug_assert_eq!(args.len(), 3);

            let s = args[0];
            let start = args[1];
            let end = args[2];

            debug_assert_eq!(heap[s], pgm.str_view_ty_tag, "{:?}", loc);

            let view_len = heap[s + 2] - heap[s + 1];

            if start > view_len {
                panic!(
                    "StrView.substr start index {} is larger than view length {}",
                    start, view_len
                );
            }

            if end > view_len {
                panic!(
                    "{}: StrView.substr({}, {}) out of bounds, view length = {}",
                    loc_display(loc),
                    start,
                    end,
                    view_len
                );
            }

            if start > end {
                panic!("StrView.substr start index larger than end index");
            }

            heap.allocate_str_view(
                pgm.str_view_ty_tag,
                heap[s + 3],
                start + heap[s + 1],
                end + heap[s + 1],
            )
        }

        BuiltinFun::StrViewLen => {
            debug_assert_eq!(args.len(), 1);

            let s = args[0];
            debug_assert_eq!(heap[s], pgm.str_view_ty_tag, "{:?}", loc);

            heap[s + 2] - heap[s + 1]
        }

        BuiltinFun::StrViewStartsWith => {
            debug_assert_eq!(args.len(), 2);

            let s1 = args[0];
            let s2 = args[1];

            debug_assert_eq!(heap[s1], pgm.str_view_ty_tag);
            debug_assert_eq!(heap[s2], pgm.str_ty_tag);

            let s1_start = heap[s1 + 1];
            let s1_end = heap[s1 + 2];
            let s1_len = s1_end - s1_start;
            let s2_len = heap[s2 + 1];

            if s1_len < s2_len {
                return pgm.bool_alloc(false);
            }

            let s1_payload_byte_addr = {
                let viewed_str = heap[s1 + 3];
                let skip_tag_and_len = viewed_str + 2;
                skip_tag_and_len * 8
            };

            let s2_payload_byte_addr = (s2 + 2) * 8;

            let heap_bytes: &[u8] = cast_slice(&heap.values);

            let eq = heap_bytes[(s1_payload_byte_addr + s1_start) as usize
                ..(s1_payload_byte_addr + s1_start + s2_len) as usize]
                == heap_bytes
                    [s2_payload_byte_addr as usize..(s2_payload_byte_addr + s2_len) as usize];

            pgm.bool_alloc(eq)
        }

        BuiltinFun::StrViewIsEmpty => {
            debug_assert_eq!(args.len(), 1);
            let s = args[0];
            debug_assert_eq!(heap[s], pgm.str_view_ty_tag);

            let s_start = heap[s + 1];
            let s_end = heap[s + 2];

            pgm.bool_alloc(s_start == s_end)
        }

        BuiltinFun::StrViewToStr => {
            debug_assert_eq!(args.len(), 1);
            let s = args[0];
            debug_assert_eq!(heap[s], pgm.str_view_ty_tag);
            let str_view_bytes = heap.str_view_bytes(s).to_vec();
            heap.allocate_str(pgm.str_ty_tag, &str_view_bytes)
        }
    }
}
