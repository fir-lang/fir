type StrBuf:
    # UTF-8 encoding of the string.
    bytes: Vec[U8]

impl StrBuf:
    fn withCapacity(cap: U32): StrBuf =
        StrBuf(bytes = Vec.withCapacity(cap))

    fn len(self): U32 =
        self.bytes.len

    fn clear(self) =
        self.bytes.clear()

    fn push(self, char: Char) =
        let code = char.value
        let len = char.lenUtf8()
        if len == 1u32:
            self.bytes.push(code as U8)
        elif len == 2u32:
            let b0 = ((code >> 6u32) & 0x1Fu32) as U8 | 0b1100_0000u8
            let b1 = (code & 0x3Fu32) as U8 | 0b1000_0000u8
            self.bytes.push(b0)
            self.bytes.push(b1)
        elif len == 3u32:
            let b0 = ((code >> 12u32) & 0x0Fu32) as U8 | 0b1110_0000u8
            let b1 = ((code >> 6u32) & 0x3Fu32) as U8 | 0b1000_0000u8
            let b2 = (code & 0x3Fu32) as U8 | 0b1000_0000u8
            self.bytes.push(b0)
            self.bytes.push(b1)
            self.bytes.push(b2)
        else:
            let b0 = ((code >> 18u32) & 0x07u32) as U8 | 0b1111_0000u8
            let b1 = ((code >> 12u32) & 0x3Fu32) as U8 | 0b1000_0000u8
            let b2 = ((code >> 6u32) & 0x3Fu32) as U8 | 0b1000_0000u8
            let b3 = (code & 0x3Fu32) as U8 | 0b1000_0000u8
            self.bytes.push(b0)
            self.bytes.push(b1)
            self.bytes.push(b2)
            self.bytes.push(b3)

    fn toStr(self): Str =
        Str.fromUtf8Vec(self.bytes)
