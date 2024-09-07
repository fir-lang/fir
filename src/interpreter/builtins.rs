use crate::ast::Loc;
use crate::interpreter::*;

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
    ArrayGet,
    ArrayLen,
    ArrayNew,
    ArraySet,

    // I32
    I32Add,
    I32Cmp,
    I32Eq,
    I32Mul,
    I32Sub,
    I32ToStr,

    // U32
    U32Add,
    U32Cmp,
    U32Eq,
    U32Mul,
    U32Sub,
    U32ToStr,

    // I8
    I8Add,
    I8Cmp,
    I8Eq,
    I8Mul,
    I8Sub,
    I8ToStr,

    // U8
    U8Add,
    U8Cmp,
    U8Eq,
    U8Mul,
    U8Sub,
    U8ToStr,

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

            panic!("{}: PANIC: {}", LocDisplay(loc), msg);
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

        BuiltinFun::ArrayNew => {
            debug_assert_eq!(args.len(), 1);

            let cap = args[0];
            debug_assert_eq!(heap[cap], pgm.i32_ty_tag);
            let cap = heap[cap + 1];
            heap.allocate_array(pgm.array_ty_tag, cap)
        }

        BuiltinFun::ArrayLen => {
            debug_assert_eq!(args.len(), 1);

            let array = args[0];
            debug_assert_eq!(heap[array], pgm.array_ty_tag);
            let len = heap[array + 1];
            heap.allocate_i32(pgm.i32_ty_tag, len as i32)
        }

        BuiltinFun::ArraySet => {
            debug_assert_eq!(args.len(), 3);

            let array = args[0];
            debug_assert_eq!(heap[array], pgm.array_ty_tag);

            let idx = args[1];
            debug_assert_eq!(heap[idx], pgm.i32_ty_tag);

            let elem = args[2];

            let array_len = heap[array + 1];
            let idx = heap[idx + 1];
            assert!(idx < array_len);

            heap[array + 2 + idx] = elem;
            elem
        }

        BuiltinFun::ArrayGet => {
            debug_assert_eq!(args.len(), 2);

            let array = args[0];
            debug_assert_eq!(heap[array], pgm.array_ty_tag);

            let idx = args[1];
            debug_assert_eq!(heap[idx], pgm.i32_ty_tag);

            let array_len = heap[array + 1];
            let idx = heap[idx + 1];
            assert!(idx < array_len);

            let value = heap[array + 2 + idx];
            if value == 0 {
                panic!("Reading uninitialized array element");
            }
            value
        }

        BuiltinFun::StrLen => {
            debug_assert_eq!(args.len(), 1);
            let str = args[0];
            debug_assert_eq!(heap[str], pgm.str_ty_tag);
            heap.allocate_i32(pgm.i32_ty_tag, heap[str + 1] as i32)
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
            debug_assert_eq!(heap[byte_start], pgm.i32_ty_tag);
            debug_assert_eq!(heap[byte_end], pgm.i32_ty_tag);

            let str_len = heap[str + 1];
            let byte_start = heap[byte_start + 1];
            let byte_end = heap[byte_end + 1];

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

            debug_assert_eq!(heap[i1], pgm.i32_ty_tag);
            debug_assert_eq!(heap[i2], pgm.i32_ty_tag);

            let i1 = heap[i1 + 1];
            let i2 = heap[i2 + 1];

            heap.allocate_i32(pgm.i32_ty_tag, (i1 as i32) + (i2 as i32))
        }

        BuiltinFun::I32Sub => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            debug_assert_eq!(heap[i1], pgm.i32_ty_tag);
            debug_assert_eq!(heap[i2], pgm.i32_ty_tag);

            let i1 = heap[i1 + 1];
            let i2 = heap[i2 + 1];

            heap.allocate_i32(pgm.i32_ty_tag, (i1 as i32) - (i2 as i32))
        }

        BuiltinFun::I32Mul => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            debug_assert_eq!(heap[i1], pgm.i32_ty_tag);
            debug_assert_eq!(heap[i2], pgm.i32_ty_tag);

            let i1 = heap[i1 + 1];
            let i2 = heap[i2 + 1];

            heap.allocate_i32(pgm.i32_ty_tag, (i1 as i32) * (i2 as i32))
        }

        BuiltinFun::I32Cmp => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            debug_assert_eq!(heap[i1], pgm.i32_ty_tag);
            debug_assert_eq!(heap[i2], pgm.i32_ty_tag);

            let ordering_ty_con = pgm.ty_cons.get("Ordering").unwrap_or_else(|| {
                panic!("__cmp was called, but the Ordering type is not defined")
            });

            let i1 = heap[i1 + 1];
            let i2 = heap[i2 + 1];

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

            debug_assert_eq!(heap[i1], pgm.i32_ty_tag, "{}", LocDisplay(loc));
            debug_assert_eq!(heap[i2], pgm.i32_ty_tag, "{}", LocDisplay(loc));

            let i1 = heap[i1 + 1];
            let i2 = heap[i2 + 1];

            pgm.bool_alloc(i1 == i2)
        }

        BuiltinFun::I32ToStr => {
            debug_assert_eq!(args.len(), 1);
            let obj = args[0];
            debug_assert_eq!(heap[obj], pgm.i32_ty_tag);
            let i = heap[obj + 1];
            heap.allocate_str(pgm.str_ty_tag, format!("{}", i as i32).as_bytes())
        }

        BuiltinFun::U32Add => {
            debug_assert_eq!(args.len(), 2);

            let u1 = args[0];
            let u2 = args[1];

            debug_assert_eq!(heap[u1], pgm.u32_ty_tag);
            debug_assert_eq!(heap[u2], pgm.u32_ty_tag);

            let u1 = heap[u1 + 1];
            let u2 = heap[u2 + 1];

            heap.allocate_u32(pgm.u32_ty_tag, (u1 as u32) + (u2 as u32))
        }

        BuiltinFun::U32Sub => {
            debug_assert_eq!(args.len(), 2);

            let u1 = args[0];
            let u2 = args[1];

            debug_assert_eq!(heap[u1], pgm.u32_ty_tag);
            debug_assert_eq!(heap[u2], pgm.u32_ty_tag);

            let u1 = heap[u1 + 1];
            let u2 = heap[u2 + 1];

            heap.allocate_u32(pgm.u32_ty_tag, (u1 as u32) - (u2 as u32))
        }

        BuiltinFun::U32Mul => {
            debug_assert_eq!(args.len(), 2);

            let u1 = args[0];
            let u2 = args[1];

            debug_assert_eq!(heap[u1], pgm.u32_ty_tag);
            debug_assert_eq!(heap[u2], pgm.u32_ty_tag);

            let u1 = heap[u1 + 1];
            let u2 = heap[u2 + 1];

            heap.allocate_u32(pgm.u32_ty_tag, (u1 as u32) * (u2 as u32))
        }

        BuiltinFun::U32Cmp => {
            debug_assert_eq!(args.len(), 2);

            let u1 = args[0];
            let u2 = args[1];

            debug_assert_eq!(heap[u1], pgm.u32_ty_tag);
            debug_assert_eq!(heap[u2], pgm.u32_ty_tag);

            let ordering_ty_con = pgm.ty_cons.get("Ordering").unwrap_or_else(|| {
                panic!("__cmp was called, but the Ordering type is not defined")
            });

            let u1 = heap[u1 + 1];
            let u2 = heap[u2 + 1];

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

            debug_assert_eq!(heap[u1], pgm.u32_ty_tag, "{}", LocDisplay(loc));
            debug_assert_eq!(heap[u2], pgm.u32_ty_tag, "{}", LocDisplay(loc));

            let u1 = heap[u1 + 1];
            let u2 = heap[u2 + 1];

            pgm.bool_alloc(u1 == u2)
        }

        BuiltinFun::U32ToStr => {
            debug_assert_eq!(args.len(), 1);
            let obj = args[0];
            debug_assert_eq!(heap[obj], pgm.u32_ty_tag);
            let u = heap[obj + 1];
            heap.allocate_str(pgm.str_ty_tag, format!("{}", u as u32).as_bytes())
        }

        BuiltinFun::I8Add => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            debug_assert_eq!(heap[i1], pgm.i8_ty_tag);
            debug_assert_eq!(heap[i2], pgm.i8_ty_tag);

            let i1 = heap[i1 + 1];
            let i2 = heap[i2 + 1];

            heap.allocate_i8(pgm.i8_ty_tag, (i1 as i8) + (i2 as i8))
        }

        BuiltinFun::I8Sub => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            debug_assert_eq!(heap[i1], pgm.i8_ty_tag);
            debug_assert_eq!(heap[i2], pgm.i8_ty_tag);

            let i1 = heap[i1 + 1];
            let i2 = heap[i2 + 1];

            heap.allocate_i8(pgm.i8_ty_tag, (i1 as i8) - (i2 as i8))
        }

        BuiltinFun::I8Mul => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            debug_assert_eq!(heap[i1], pgm.i8_ty_tag);
            debug_assert_eq!(heap[i2], pgm.i8_ty_tag);

            let i1 = heap[i1 + 1];
            let i2 = heap[i2 + 1];

            heap.allocate_i8(pgm.i8_ty_tag, (i1 as i8) * (i2 as i8))
        }

        BuiltinFun::I8Cmp => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            debug_assert_eq!(heap[i1], pgm.i8_ty_tag);
            debug_assert_eq!(heap[i2], pgm.i8_ty_tag);

            let ordering_ty_con = pgm.ty_cons.get("Ordering").unwrap_or_else(|| {
                panic!("__cmp was called, but the Ordering type is not defined")
            });

            let i1 = heap[i1 + 1];
            let i2 = heap[i2 + 1];

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

            debug_assert_eq!(heap[i1], pgm.i8_ty_tag, "{}", LocDisplay(loc));
            debug_assert_eq!(heap[i2], pgm.i8_ty_tag, "{}", LocDisplay(loc));

            let i1 = heap[i1 + 1];
            let i2 = heap[i2 + 1];

            pgm.bool_alloc(i1 == i2)
        }

        BuiltinFun::I8ToStr => {
            debug_assert_eq!(args.len(), 1);
            let obj = args[0];
            debug_assert_eq!(heap[obj], pgm.i8_ty_tag);
            let i = heap[obj + 1];
            heap.allocate_str(pgm.str_ty_tag, format!("{}", i as i8).as_bytes())
        }

        BuiltinFun::U8Add => {
            debug_assert_eq!(args.len(), 2);

            let u1 = args[0];
            let u2 = args[1];

            debug_assert_eq!(heap[u1], pgm.u8_ty_tag);
            debug_assert_eq!(heap[u2], pgm.u8_ty_tag);

            let u1 = heap[u1 + 1];
            let u2 = heap[u2 + 1];

            heap.allocate_u8(pgm.u8_ty_tag, (u1 as u8) + (u2 as u8))
        }

        BuiltinFun::U8Sub => {
            debug_assert_eq!(args.len(), 2);

            let u1 = args[0];
            let u2 = args[1];

            debug_assert_eq!(heap[u1], pgm.u8_ty_tag);
            debug_assert_eq!(heap[u2], pgm.u8_ty_tag);

            let u1 = heap[u1 + 1];
            let u2 = heap[u2 + 1];

            heap.allocate_u8(pgm.u8_ty_tag, (u1 as u8) - (u2 as u8))
        }

        BuiltinFun::U8Mul => {
            debug_assert_eq!(args.len(), 2);

            let u1 = args[0];
            let u2 = args[1];

            debug_assert_eq!(heap[u1], pgm.u8_ty_tag);
            debug_assert_eq!(heap[u2], pgm.u8_ty_tag);

            let u1 = heap[u1 + 1];
            let u2 = heap[u2 + 1];

            heap.allocate_u8(pgm.u8_ty_tag, (u1 as u8) * (u2 as u8))
        }

        BuiltinFun::U8Cmp => {
            debug_assert_eq!(args.len(), 2);

            let u1 = args[0];
            let u2 = args[1];

            debug_assert_eq!(heap[u1], pgm.u8_ty_tag);
            debug_assert_eq!(heap[u2], pgm.u8_ty_tag);

            let ordering_ty_con = pgm.ty_cons.get("Ordering").unwrap_or_else(|| {
                panic!("__cmp was called, but the Ordering type is not defined")
            });

            let u1 = heap[u1 + 1];
            let u2 = heap[u2 + 1];

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

            debug_assert_eq!(heap[u1], pgm.u8_ty_tag, "{}", LocDisplay(loc));
            debug_assert_eq!(heap[u2], pgm.u8_ty_tag, "{}", LocDisplay(loc));

            let u1 = heap[u1 + 1];
            let u2 = heap[u2 + 1];

            pgm.bool_alloc(u1 == u2)
        }

        BuiltinFun::U8ToStr => {
            debug_assert_eq!(args.len(), 1);
            let obj = args[0];
            debug_assert_eq!(heap[obj], pgm.u8_ty_tag);
            let u = heap[obj + 1];
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
            debug_assert_eq!(heap[start], pgm.i32_ty_tag, "{:?}", loc);
            debug_assert_eq!(heap[end], pgm.i32_ty_tag, "{:?}", loc);

            let start = heap[start + 1];
            let end = heap[end + 1];

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
                    LocDisplay(loc),
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

            let len = heap[s + 2] - heap[s + 1];
            heap.allocate_i32(pgm.i32_ty_tag, len as i32)
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
