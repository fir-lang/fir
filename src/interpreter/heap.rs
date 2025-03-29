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
        debug_assert!((index as usize) < self.hp);
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

    pub fn allocate_str(&mut self, str_tag: u64, array_tag: u64, string: &[u8]) -> u64 {
        let size_words = string.len().div_ceil(8);
        let array = self.allocate(size_words + 2);
        self[array] = array_tag;
        self[array + 1] = string.len() as u64;
        let bytes: &mut [u8] =
            &mut cast_slice_mut::<u64, u8>(&mut self.values[array as usize + 2..])[..string.len()];
        bytes.copy_from_slice(string);

        let alloc = self.allocate(4);
        self[alloc] = str_tag;
        self[alloc + 1] = array;
        self[alloc + 2] = 0;
        self[alloc + 3] = string.len() as u64;
        alloc
    }

    pub fn allocate_str_view(
        &mut self,
        ty_tag: u64,
        str: u64,
        byte_start: u32,
        byte_len: u32,
    ) -> u64 {
        let array = self[str + 1];
        let start = val_as_u32(self[str + 2]);

        let new_str = self.allocate(4);
        self[new_str] = ty_tag;
        self[new_str + 1] = array;
        self[new_str + 2] = u32_as_val(start + byte_start);
        self[new_str + 3] = u32_as_val(byte_len);

        new_str
    }

    pub fn str_bytes(&self, str_addr: u64) -> &[u8] {
        let str_byte_array = self[str_addr + 1];
        let str_start = val_as_u32(self[str_addr + 2]);
        let str_len = val_as_u32(self[str_addr + 3]);
        &cast_slice::<u64, u8>(&self.values[(str_byte_array + 2) as usize..])
            [str_start as usize..(str_start + str_len) as usize]
    }

    pub fn allocate_constr(&mut self, type_tag: u64) -> u64 {
        let alloc = self.allocate(2);
        self[alloc] = CONSTR_TYPE_TAG;
        self[alloc + 1] = type_tag;
        alloc
    }

    pub fn allocate_fun(&mut self, fun_idx: u64) -> u64 {
        let alloc = self.allocate(2);
        self[alloc] = FUN_TYPE_TAG;
        self[alloc + 1] = fun_idx;
        alloc
    }

    pub fn allocate_method(&mut self, receiver: u64, fun_idx: u64) -> u64 {
        let alloc = self.allocate(3);
        self[alloc] = METHOD_TYPE_TAG;
        self[alloc + 1] = receiver;
        self[alloc + 2] = fun_idx;
        alloc
    }
}
