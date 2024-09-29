# Immuable, UTF-8 encoded strings.
type Str:
    # UTF-8 encoding of the string.
    _bytes: Array[U8]

    # Where the string starts in `bytes`.
    _start: U32

    # Length of the encoding.
    _len: U32

impl Str:
    # Copied the bytes, does not validate UTF-8.
    fn fromUtf8Vec(bytes: Vec[U8]): Str =
        let copied = Array.new(bytes.len())
        for i in 0u32 .. bytes.len():
            copied.set(i, bytes.get(i))
        Str(_bytes = copied, _start = 0, _len = copied.len())

    # UTF-8 encoding size of the string.
    fn len(self): U32 = self._len

    fn isEmpty(self): Bool = self.len() == 0

    fn substr(self, byteStart: U32, byteEnd: U32): Str =
        if byteStart > self.len():
            panic("Str.substr: byteStart (`byteStart`) > len (`self.len()`)")

        if byteEnd > self.len():
            panic("Str.substr: byteEnd (`byteEnd`) > len (`self.len()`)")

        if byteStart > byteEnd:
            panic("Str.substr: byteStart (`byteStart`) > byteEnd (`byteEnd`)")

        Str(
            _bytes = self._bytes,
            _start = self._start + byteStart,
            _len = byteEnd - byteStart,
        )

    fn startsWith(self, prefix: Str): Bool =
        if self.len() < prefix.len():
            return Bool.False

        for i in 0u32 .. prefix.len():
            if self._bytes.get(i + self._start) != prefix._bytes.get(i + prefix._start):
                return Bool.False

        Bool.True

impl Eq for Str:
    fn __eq(self, other: Str): Bool =
        if self.len() != other.len():
            return Bool.False

        for i in 0u32 .. self.len():
            if self._bytes.get(i + self._start) != other._bytes.get(i + other._start):
                return Bool.False

        Bool.True

impl ToStr for Str:
    fn toStr(self): Str = self
