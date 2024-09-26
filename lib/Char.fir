# TODO: We may want to allow unnamed fields: `type Char(U32)`.
type Char:
    value: U32

impl Eq for Char:
    fn __eq(self, other: Char): Bool =
        self.value == other.value

impl Char:
    fn fromU32(value: U32): Option[Char] =
        if value >= 0x110000 || (value >= 0xD800 && value <= 0xDFFF):
            return Option.None

        Option.Some(Char(value = value))

    fn lenUtf8(self): U32 =
        if self.value < 0x80:
            1
        elif self.value < 0x800:
            2
        elif self.value < 0x10000:
            3
        else:
            4
