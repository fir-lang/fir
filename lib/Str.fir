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
        for i in range(0u32, bytes.len()):
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

        for i in range(0u32, prefix.len()):
            if self._bytes.get(i + self._start) != prefix._bytes.get(i + prefix._start):
                return Bool.False

        Bool.True

    # Get the character at given byte index. Panics if the byte is not a first byte of a UTF-8
    # code point.
    fn charAt(self, byteIndex: U32): Char =
        let byte = self._bytes.get(byteIndex)

        if byte < 128:
            return Char(_codePoint = byte as U32)

        # Check continuation bit.
        if byte & 0b1100_0000 == 0b1000_0000:
            panic("Byte at index `byteIndex` is not a code point start")

        if byte & 0b1110_0000 == 0b1100_0000:
            # 2 bytes
            let b0 = (byte & 0b11111) as U32
            let b1 = (self._bytes.get(byteIndex + 1) & 0b111111) as U32
            Char(_codePoint = (b0 << 6) | b1)
        elif byte & 0b1111_0000 == 0b1110_0000:
            # 3 bytes
            let b0 = (byte & 0b1111) as U32
            let b1 = (self._bytes.get(byteIndex + 1) & 0b111111) as U32
            let b2 = (self._bytes.get(byteIndex + 2) & 0b111111) as U32
            Char(_codePoint = (b0 << 12) | (b1 << 6) | b2)
        else:
            # 4 bytes
            let b0 = (byte & 0b111) as U32
            let b1 = (self._bytes.get(byteIndex + 1) & 0b111111) as U32
            let b2 = (self._bytes.get(byteIndex + 2) & 0b111111) as U32
            let b3 = (self._bytes.get(byteIndex + 3) & 0b111111) as U32
            Char(_codePoint = (b0 << 18) | (b1 << 12) | (b2 << 6) | b3)

    fn chars(self): CharIter =
        CharIter(
            _bytes = self._bytes,
            _idx = self._start,
            _end = self._start + self._len,
        )

impl Eq for Str:
    fn __eq(self, other: Str): Bool =
        if self.len() != other.len():
            return Bool.False

        for i in range(0u32, self.len()):
            if self._bytes.get(i + self._start) != other._bytes.get(i + other._start):
                return Bool.False

        Bool.True

impl ToStr for Str:
    fn toStr(self): Str = self

type CharIter:
    # UTF-8 encoding of the string.
    _bytes: Array[U8]

    # Current index into `_bytes`.
    _idx: U32

    # End index.
    _end: U32

impl Iterator for CharIter:
    type Item = Char

    fn next(self): Option[Char] =
        if self._idx == self._end:
            return Option.None

        let char = _charAt(self._bytes, self._idx)
        let charLength = char.lenUtf8()
        self._idx += charLength
        Option.Some(char)

fn _charAt(bytes: Array[U8], idx: U32): Char =
    let byte = bytes.get(idx)

    if byte < 128:
        return Char(_codePoint = byte as U32)

    # Check continuation bit.
    if byte & 0b1100_0000 == 0b1000_0000:
        panic("Byte at index `idx` is not a code point start")

    if byte & 0b1110_0000 == 0b1100_0000:
        # 2 bytes
        let b0 = (byte & 0b11111) as U32
        let b1 = (bytes.get(idx + 1) & 0b111111) as U32
        Char(_codePoint = (b0 << 6) | b1)
    elif byte & 0b1111_0000 == 0b1110_0000:
        # 3 bytes
        let b0 = (byte & 0b1111) as U32
        let b1 = (bytes.get(idx + 1) & 0b111111) as U32
        let b2 = (bytes.get(idx + 2) & 0b111111) as U32
        Char(_codePoint = (b0 << 12) | (b1 << 6) | b2)
    else:
        # 4 bytes
        let b0 = (byte & 0b111) as U32
        let b1 = (bytes.get(idx + 1) & 0b111111) as U32
        let b2 = (bytes.get(idx + 2) & 0b111111) as U32
        let b3 = (bytes.get(idx + 3) & 0b111111) as U32
        Char(_codePoint = (b0 << 18) | (b1 << 12) | (b2 << 6) | b3)
