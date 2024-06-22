use crate::interpreter::*;

use bytemuck::cast_slice;

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
        &self.values[index as usize]
    }
}

impl std::ops::IndexMut<u64> for Heap {
    fn index_mut(&mut self, index: u64) -> &mut Self::Output {
        &mut self.values[index as usize]
    }
}

impl Heap {
    pub fn new() -> Self {
        Heap {
            values: vec![0; INITIAL_HEAP_SIZE_WORDS].into_boxed_slice(),
            hp: 0,
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

    pub fn allocate_str(&mut self, string: &[u8]) -> u64 {
        let size_words = string.len().div_ceil(8);
        let alloc = self.allocate(size_words + 2);
        self[alloc] = STR_TYPE_TAG;
        self[alloc + 1] = string.len() as u64;

        let bytes_start_word = (alloc as usize) + 2;
        let bytes_end_word = bytes_start_word + size_words;

        let bytes: &mut [u8] = cast_slice_mut(&mut self.values[bytes_start_word..=bytes_end_word]);
        bytes[..string.len()].copy_from_slice(string);

        alloc
    }

    pub fn str_bytes(&self, str_addr: u64) -> &[u8] {
        let str_len_bytes = self[str_addr + 1];
        let str_payload_byte_addr = (str_addr + 2) * 8;
        &cast_slice(&self.values)
            [str_payload_byte_addr as usize..(str_payload_byte_addr + str_len_bytes) as usize]
    }

    pub fn allocate_i32(&mut self, i: i32) -> u64 {
        let alloc = self.allocate(2);
        self[alloc] = I32_TYPE_TAG;
        self[alloc + 1] = (i as u32) as u64;
        alloc
    }

    pub fn allocate_bool(&mut self, b: bool) -> u64 {
        let alloc = self.allocate(1);
        self[alloc] = if b { TRUE_TYPE_TAG } else { FALSE_TYPE_TAG };
        alloc
    }

    pub fn allocate_constr(&mut self, type_tag: u64) -> u64 {
        let alloc = self.allocate(2);
        self[alloc] = CONSTR_TYPE_TAG;
        self[alloc + 1] = type_tag;
        alloc
    }

    pub fn allocate_top_fun(&mut self, fun_idx: u64) -> u64 {
        let alloc = self.allocate(2);
        self[alloc] = TOP_FUN_TYPE_TAG;
        self[alloc + 1] = fun_idx;
        alloc
    }

    pub fn allocate_str_view(&mut self, start_byte: u64, end_byte: u64, string: u64) -> u64 {
        let alloc = self.allocate(4);
        self[alloc] = STR_VIEW_TYPE_TAG;
        self[alloc + 1] = start_byte;
        self[alloc + 2] = end_byte;
        self[alloc + 3] = string;
        alloc
    }

    pub fn allocate_array(&mut self, cap: u64, elem: u64) -> u64 {
        let alloc = self.allocate(2 + cap as usize);
        self[alloc] = ARRAY_TYPE_TAG;
        self[alloc + 1] = cap;
        for i in 0..cap {
            self[alloc + 2 + i] = elem;
        }
        alloc
    }
}
