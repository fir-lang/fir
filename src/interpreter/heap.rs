use crate::interpreter::*;
use crate::lowering::{CON_CON_IDX, FUN_CON_IDX, Repr};

use bytemuck::{cast_slice, cast_slice_mut};

pub const ARRAY_DATA_ADDR_FIELD_IDX: u64 = 1;
pub const ARRAY_LEN_FIELD_IDX: u64 = 2;

/// Heap is just a growable array of words. A word is 8 bytes, to easily allow references larger
/// than 4 bytes, which we may need when interpreting the bootstrapping compiler without a GC.
#[derive(Debug)]
pub struct Heap {
    pub values: Box<[u64]>,
    hp: usize,
}

impl std::ops::Index<u64> for Heap {
    type Output = u64;

    fn index(&self, index: u64) -> &Self::Output {
        debug_assert!(
            (index as usize) < self.hp,
            "index={}, hp={}",
            index,
            self.hp
        );
        &self.values[index as usize]
    }
}

impl std::ops::IndexMut<u64> for Heap {
    fn index_mut(&mut self, index: u64) -> &mut Self::Output {
        debug_assert!((index as usize) < self.hp);
        &mut self.values[index as usize]
    }
}

impl Heap {
    pub fn new() -> Self {
        // Heap pointer starts from 1. Address 0 is used as "null" or "uninitialized" marker in
        // arrays.
        Heap {
            values: vec![0; INITIAL_HEAP_SIZE_WORDS].into_boxed_slice(),
            hp: 1,
        }
    }

    pub fn allocate(&mut self, size: usize) -> u64 {
        if self.hp + size > self.values.len() {
            let mut new_values: Box<[u64]> = vec![0; self.values.len() * 2].into_boxed_slice();
            new_values[0..self.hp].copy_from_slice(&self.values[0..self.hp]);
            self.values = new_values;
        }

        let hp = self.hp;
        self.hp += size;
        hp as u64
    }

    // TODO: These should be allocated once and reused.
    pub fn allocate_tag(&mut self, tag: u64) -> u64 {
        let alloc = self.allocate(1);
        self[alloc] = tag;
        alloc
    }

    // Allocate data, then allocate a separate `Array` object with:
    // - Header
    // - Pointer to data
    // - Length of data (in number of elements)
    // This layout allows slicing the array.
    pub fn allocate_array(&mut self, tag: u64, repr: Repr, len: u32) -> u64 {
        let len_words = (len as usize) * repr.elem_size_in_bytes().div_ceil(8);
        // Allocate in one go. Bump alloc is cheap so we could also allocate separately.
        let array_obj_addr = self.allocate(len_words + 3);
        let data_addr = array_obj_addr + 3;
        self[array_obj_addr] = tag;
        assert_eq!(ARRAY_DATA_ADDR_FIELD_IDX, 1);
        self[array_obj_addr + 1] = data_addr
            * match repr {
                Repr::U8 => 8,
                Repr::U32 => 2,
                Repr::U64 => 1,
            };
        assert_eq!(ARRAY_LEN_FIELD_IDX, 2);
        self[array_obj_addr + 2] = u32_as_val(len);
        self.values[data_addr as usize..(data_addr as usize) + len_words].fill(0);
        array_obj_addr
    }

    pub fn array_slice(
        &mut self,
        array: u64,
        start: u32,
        end: u32,
        tag: u64,
        loc: &ast::Loc,
        call_stack: &[Frame],
    ) -> u64 {
        let array_len = val_as_u32(self[array + ARRAY_LEN_FIELD_IDX]);
        if start > array_len || end > array_len || start > end {
            let mut msg_str = format!(
                "{}: OOB array slice (start = {}, end = {}, len = {})\n",
                loc_display(loc),
                start,
                end,
                array_len
            );
            msg_str.push_str("\nFIR STACK:\n");
            crate::interpreter::write_call_stack(call_stack, &mut msg_str);
            panic!("{}", msg_str);
        }

        let data_addr = self[array + ARRAY_DATA_ADDR_FIELD_IDX];
        let array_obj_addr = self.allocate(3);
        self[array_obj_addr] = tag;
        assert_eq!(ARRAY_DATA_ADDR_FIELD_IDX, 1);
        self[array_obj_addr + 1] = data_addr + u64::from(start);
        assert_eq!(ARRAY_LEN_FIELD_IDX, 2);
        self[array_obj_addr + 2] = u32_as_val(end - start);
        array_obj_addr
    }

    pub fn array_set(
        &mut self,
        array: u64,
        idx: u32,
        val: u64,
        repr: Repr,
        loc: &ast::Loc,
        call_stack: &[Frame],
    ) {
        let array_len = val_as_u32(self[array + ARRAY_LEN_FIELD_IDX]);
        if idx >= array_len {
            let mut msg_str = format!(
                "{}: OOB array access (idx = {}, len = {})\n",
                loc_display(loc),
                idx,
                array_len
            );
            msg_str.push_str("\nFIR STACK:\n");
            crate::interpreter::write_call_stack(call_stack, &mut msg_str);
            panic!("{}", msg_str);
        }

        let data = self[array + ARRAY_DATA_ADDR_FIELD_IDX];

        match repr {
            Repr::U8 => {
                let payload: &mut [u8] = &mut cast_slice_mut(&mut self.values)[data as usize..];
                payload[idx as usize] = val_as_u8(val);
            }

            Repr::U32 => {
                let payload: &mut [u32] = &mut cast_slice_mut(&mut self.values)[data as usize..];
                payload[idx as usize] = val_as_u32(val);
            }

            Repr::U64 => {
                let payload: &mut [u64] = &mut cast_slice_mut(&mut self.values)[data as usize..];
                payload[idx as usize] = val;
            }
        }
    }

    pub fn array_copy_within(
        &mut self,
        array: u64,
        src: u32,
        dst: u32,
        len: u32,
        repr: Repr,
        loc: &ast::Loc,
        call_stack: &[Frame],
    ) {
        let array_len = val_as_u32(self[array + ARRAY_LEN_FIELD_IDX]);
        if src + len > array_len || dst + len > array_len {
            let mut msg_str = format!("{}: OOB array access\n", loc_display(loc));
            msg_str.push_str("\nFIR STACK:\n");
            crate::interpreter::write_call_stack(call_stack, &mut msg_str);
            panic!("{}", msg_str);
        }

        let data = self[array + ARRAY_DATA_ADDR_FIELD_IDX];

        match repr {
            Repr::U8 => {
                let payload: &mut [u8] = &mut cast_slice_mut(&mut self.values)[data as usize..];
                payload.copy_within(src as usize..((src + len) as usize), dst as usize);
            }

            Repr::U32 => {
                let payload: &mut [u32] = &mut cast_slice_mut(&mut self.values)[data as usize..];
                payload.copy_within(src as usize..((src + len) as usize), dst as usize);
            }

            Repr::U64 => {
                let payload: &mut [u64] = &mut cast_slice_mut(&mut self.values)[data as usize..];
                payload.copy_within(src as usize..((src + len) as usize), dst as usize);
            }
        }
    }

    pub fn array_get(
        &mut self,
        array: u64,
        idx: u32,
        repr: Repr,
        loc: &ast::Loc,
        call_stack: &[Frame],
    ) -> u64 {
        let array_len = val_as_u32(self[array + ARRAY_LEN_FIELD_IDX]);
        if idx >= array_len {
            let mut msg_str = format!(
                "{}: OOB array access (idx = {}, len = {})\n",
                loc_display(loc),
                idx,
                array_len
            );
            msg_str.push_str("\nFIR STACK:\n");
            crate::interpreter::write_call_stack(call_stack, &mut msg_str);
            panic!("{}", msg_str);
        }
        let data = self[array + ARRAY_DATA_ADDR_FIELD_IDX];
        match repr {
            Repr::U8 => {
                let payload: &[u8] = &cast_slice(&self.values)[data as usize..];
                u8_as_val(payload[idx as usize])
            }
            Repr::U32 => {
                let payload: &[u32] = &cast_slice(&self.values)[data as usize..];
                u32_as_val(payload[idx as usize])
            }
            Repr::U64 => {
                let payload: &[u64] = &cast_slice(&self.values)[data as usize..];
                payload[idx as usize]
            }
        }
    }

    pub fn allocate_str(
        &mut self,
        str_tag: u64,
        array_tag: u64,
        array_repr: Repr,
        string: &[u8],
    ) -> u64 {
        let array = self.allocate_array(array_tag, array_repr, string.len() as u32);
        let data = self[array + ARRAY_DATA_ADDR_FIELD_IDX];

        let bytes: &mut [u8] =
            &mut cast_slice_mut::<u64, u8>(&mut self.values)[data as usize..][..string.len()];
        bytes.copy_from_slice(string);

        let alloc = self.allocate(2);
        self[alloc] = str_tag;
        self[alloc + 1] = array; // _bytes: Array[U8]
        alloc
    }

    #[allow(unused)]
    pub fn allocate_str_view(
        &mut self,
        str_tag: u64,
        array_u8_tag: u64,
        str: u64,
        byte_start: u32,
        byte_len: u32,
        loc: &ast::Loc,
        call_stack: &[Frame],
    ) -> u64 {
        let array = self[str + 1];
        let sliced_array = self.array_slice(
            array,
            byte_start,
            byte_start + byte_len,
            array_u8_tag,
            loc,
            call_stack,
        );

        let new_str = self.allocate(2);
        self[new_str] = str_tag;
        self[new_str + 1] = sliced_array;

        new_str
    }

    pub fn str_bytes(&self, str_addr: u64) -> &[u8] {
        let str_byte_array = self[str_addr + 1]; // _bytes: Array[U8]
        let byte_array_data = self[str_byte_array + ARRAY_DATA_ADDR_FIELD_IDX];
        let byte_array_len = self[str_byte_array + ARRAY_LEN_FIELD_IDX];
        &cast_slice::<u64, u8>(&self.values)[byte_array_data as usize..][0..byte_array_len as usize]
    }

    pub fn allocate_con(&mut self, type_tag: u64) -> u64 {
        let alloc = self.allocate(2);
        self[alloc] = CON_CON_IDX.as_u64();
        self[alloc + 1] = type_tag;
        alloc
    }

    pub fn allocate_fun(&mut self, fun_idx: u64) -> u64 {
        let alloc = self.allocate(2);
        self[alloc] = FUN_CON_IDX.as_u64();
        self[alloc + 1] = fun_idx;
        alloc
    }
}
