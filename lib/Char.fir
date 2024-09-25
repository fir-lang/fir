# TODO: We may want to allow unnamed fields: `type Char(U32)`.
type Char:
    value: U32

impl Eq for Char:
    fn __eq(self, other: Char): Bool =
        self.value == other.value

impl Char:
    fn fromU32(value: U32): Option[Char] =
        if value >= 0x110000u32 || (value >= 0xD800u32 && value <= 0xDFFFu32):
            return Option.None

        Option.Some(Char(value = value))

    fn lenUtf8(self): U32 =
        if self.value < 0x80u32:
            1u32
        elif self.value < 0x800u32:
            2u32
        elif self.value < 0x10000u32:
            3u32
        else:
            4u32
