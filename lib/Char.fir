# TODO: We may want to allow unnamed fields: `type Char(U32)`.
type Char:
    value: U32

impl Eq[Char]:
    fn __eq(self, other: Char): Bool =
        self.value == other.value

impl Char:
    fn fromU32(value: U32): Option[Char] =
        if value >= 0x110000u32 || (value >= 0xD800u32 && value <= 0xDFFFu32):
            return Option.None

        Option.Some(Char(value = value))
