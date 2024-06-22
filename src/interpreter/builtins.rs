use crate::interpreter::*;

use std::io::Write;

use bytemuck::cast_slice;
use lexgen_util::Loc;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinFun {
    // Top funs
    Panic,
    Print,
    PrintStr,
    PrintStrView,

    // Assoc funs
    ArrayNew,
    ArrayLen,
    ArraySet,
    ArrayGet,
    BoolAnd,
    BoolOr,
    BoolToString,
    I32Add,
    I32Cmp,
    I32Eq,
    I32Sub,
    I32ToString,
    StrEq,
    StrLen,
    StrSubstr,
    StrViewEq,
    StrViewIsEmpty,
    StrViewLen,
    StrViewStartsWith,
    StrViewSubstr,
}

pub fn call_builtin_fun<W: Write>(
    w: &mut W,
    pgm: &Pgm,
    heap: &mut Heap,
    fun: &BuiltinFun,
    args: Vec<u64>,
    loc: Loc,
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
            debug_assert_eq!(heap[str], STR_TYPE_TAG);

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
            debug_assert_eq!(heap[str], STR_VIEW_TYPE_TAG);

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
            debug_assert_eq!(args.len(), 2);

            let cap = args[0];
            debug_assert_eq!(heap[cap], I32_TYPE_TAG);
            let cap = heap[cap + 1];
            let elem = args[1];
            heap.allocate_array(cap, elem)
        }

        BuiltinFun::ArrayLen => {
            debug_assert_eq!(args.len(), 1);

            let array = args[0];
            debug_assert_eq!(heap[array], ARRAY_TYPE_TAG);
            let len = heap[array + 1];
            heap.allocate_i32(len as i32)
        }

        BuiltinFun::ArraySet => {
            debug_assert_eq!(args.len(), 3);

            let array = args[0];
            debug_assert_eq!(heap[array], ARRAY_TYPE_TAG);

            let idx = args[1];
            debug_assert_eq!(heap[idx], I32_TYPE_TAG);

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
            debug_assert_eq!(heap[array], ARRAY_TYPE_TAG);

            let idx = args[1];
            debug_assert_eq!(heap[idx], I32_TYPE_TAG);

            let array_len = heap[array + 1];
            let idx = heap[idx + 1];
            assert!(idx < array_len);

            heap[array + 2 + idx]
        }

        BuiltinFun::StrLen => {
            debug_assert_eq!(args.len(), 1);
            let str = args[0];
            debug_assert_eq!(heap[str], STR_TYPE_TAG);
            heap.allocate_i32(heap[str + 1] as i32)
        }

        BuiltinFun::StrEq => {
            debug_assert_eq!(args.len(), 2);

            let str1 = args[0];
            let str2 = args[1];

            debug_assert_eq!(heap[str1], STR_TYPE_TAG);
            debug_assert_eq!(heap[str2], STR_TYPE_TAG);

            let str1_len = heap[str1 + 1];
            let str2_len = heap[str2 + 1];

            if str1_len != str2_len {
                return heap.allocate_bool(false);
            }

            let len_words = str1_len.div_ceil(8);

            for i in 0..len_words {
                if heap[str1 + 2 + i] != heap[str2 + 2 + i] {
                    return heap.allocate_bool(false);
                }
            }

            heap.allocate_bool(true)
        }

        BuiltinFun::StrSubstr => {
            debug_assert_eq!(args.len(), 3);

            // Returns a `StrView`.
            let str = args[0];
            let byte_start = args[1];
            let byte_end = args[2];

            debug_assert_eq!(heap[str], STR_TYPE_TAG);
            debug_assert_eq!(heap[byte_start], I32_TYPE_TAG);
            debug_assert_eq!(heap[byte_end], I32_TYPE_TAG);

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

            heap.allocate_str_view(byte_start, byte_end, str)
        }

        BuiltinFun::I32Add => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            debug_assert_eq!(heap[i1], I32_TYPE_TAG);
            debug_assert_eq!(heap[i2], I32_TYPE_TAG);

            let i1 = heap[i1 + 1];
            let i2 = heap[i2 + 1];

            heap.allocate_i32((i1 as i32) + (i2 as i32))
        }

        BuiltinFun::I32Sub => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            debug_assert_eq!(heap[i1], I32_TYPE_TAG);
            debug_assert_eq!(heap[i2], I32_TYPE_TAG);

            let i1 = heap[i1 + 1];
            let i2 = heap[i2 + 1];

            heap.allocate_i32((i1 as i32) - (i2 as i32))
        }

        BuiltinFun::I32Cmp => {
            debug_assert_eq!(args.len(), 2);

            let i1 = args[0];
            let i2 = args[1];

            debug_assert_eq!(heap[i1], I32_TYPE_TAG);
            debug_assert_eq!(heap[i2], I32_TYPE_TAG);

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

            debug_assert_eq!(heap[i1], I32_TYPE_TAG, "{}", LocDisplay(loc));
            debug_assert_eq!(heap[i2], I32_TYPE_TAG, "{}", LocDisplay(loc));

            let i1 = heap[i1 + 1];
            let i2 = heap[i2 + 1];

            heap.allocate_bool(i1 == i2)
        }

        BuiltinFun::I32ToString => {
            debug_assert_eq!(args.len(), 1);
            let obj = args[0];
            debug_assert_eq!(heap[obj], I32_TYPE_TAG);
            let i = heap[obj + 1];
            heap.allocate_str(format!("{}", i as i32).as_bytes())
        }

        BuiltinFun::BoolAnd => {
            debug_assert_eq!(args.len(), 2);

            let b1 = args[0];
            let b2 = args[1];

            debug_assert!(heap[b1] <= TRUE_TYPE_TAG, "{:?}", loc);
            debug_assert!(heap[b2] <= TRUE_TYPE_TAG, "{:?}", loc);

            let b1 = heap[b1];
            let b2 = heap[b2];

            heap.allocate_bool(b1 == TRUE_TYPE_TAG && b2 == TRUE_TYPE_TAG)
        }

        BuiltinFun::BoolOr => {
            debug_assert_eq!(args.len(), 2);

            let b1 = args[0];
            let b2 = args[1];

            debug_assert!(heap[b1] <= TRUE_TYPE_TAG, "{:?}", loc);
            debug_assert!(heap[b2] <= TRUE_TYPE_TAG, "{:?}", loc);

            let b1 = heap[b1];
            let b2 = heap[b2];

            heap.allocate_bool(b1 == TRUE_TYPE_TAG || b2 == TRUE_TYPE_TAG)
        }

        BuiltinFun::BoolToString => {
            debug_assert_eq!(args.len(), 1);

            let b = args[0];

            debug_assert!(heap[b] <= TRUE_TYPE_TAG, "{:?}", loc);

            let b = heap[b];

            heap.allocate_str(if b == 1 {
                "Bool.True".as_bytes()
            } else {
                "Bool.False".as_bytes()
            })
        }

        BuiltinFun::StrViewEq => {
            debug_assert_eq!(args.len(), 2);

            let s1 = args[0];
            let s2 = args[1];

            debug_assert_eq!(heap[s1], STR_VIEW_TYPE_TAG, "{:?}", loc);
            debug_assert_eq!(heap[s2], STR_VIEW_TYPE_TAG, "{:?}", loc);

            let s1_start = heap[s1 + 1];
            let s1_end = heap[s1 + 2];

            let s2_start = heap[s2 + 1];
            let s2_end = heap[s2 + 2];

            if s1_end - s1_start != s2_end - s2_start {
                return heap.allocate_bool(false);
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

            heap.allocate_bool(eq)
        }

        BuiltinFun::StrViewSubstr => {
            debug_assert_eq!(args.len(), 3);

            let s = args[0];
            let start = args[1];
            let end = args[2];

            debug_assert_eq!(heap[s], STR_VIEW_TYPE_TAG, "{:?}", loc);
            debug_assert_eq!(heap[start], I32_TYPE_TAG, "{:?}", loc);
            debug_assert_eq!(heap[end], I32_TYPE_TAG, "{:?}", loc);

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

            heap.allocate_str_view(start + heap[s + 1], end + heap[s + 1], heap[s + 3])
        }

        BuiltinFun::StrViewLen => {
            debug_assert_eq!(args.len(), 1);

            let s = args[0];
            debug_assert_eq!(heap[s], STR_VIEW_TYPE_TAG, "{:?}", loc);

            let len = heap[s + 2] - heap[s + 1];
            heap.allocate_i32(len as i32)
        }

        BuiltinFun::StrViewStartsWith => {
            debug_assert_eq!(args.len(), 2);

            let s1 = args[0];
            let s2 = args[1];

            debug_assert_eq!(heap[s1], STR_VIEW_TYPE_TAG);
            debug_assert_eq!(heap[s2], STR_TYPE_TAG);

            let s1_start = heap[s1 + 1];
            let s1_end = heap[s1 + 2];
            let s1_len = s1_end - s1_start;
            let s2_len = heap[s2 + 1];

            if s1_len < s2_len {
                return heap.allocate_bool(false);
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

            heap.allocate_bool(eq)
        }

        BuiltinFun::StrViewIsEmpty => {
            debug_assert_eq!(args.len(), 1);
            let s = args[0];
            debug_assert_eq!(heap[s], STR_VIEW_TYPE_TAG);

            let s_start = heap[s + 1];
            let s_end = heap[s + 2];

            heap.allocate_bool(s_start == s_end)
        }
    }
}

struct LocDisplay(Loc);

impl std::fmt::Display for LocDisplay {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.0.line + 1, self.0.col + 1)
    }
}
