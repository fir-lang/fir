# Immutable, UTF-8 encoded strings.
type Str(
    # UTF-8 encoding of the string.
    _bytes: Array[U8],
)


# Copies the bytes, does not validate UTF-8.
Str.fromUtf8Vec(bytes: Vec[U8]) Str:
    let copied = Array.new(bytes.len())
    for i: U32 in range(u32(0), bytes.len()):
        copied.set(i, bytes.get(i))
    Str(_bytes = copied)


# UTF-8 encoding size of the string.
Str.len(self) U32:
    self._bytes.len()


Str.isEmpty(self) Bool:
    self.len() == 0


# TODO: This should check that `byteStart` and `byteEnd` are on character boundaries.
Str.substr(self, byteStart: U32, byteEnd: U32) Str:
    Str(_bytes = self._bytes.slice(byteStart, byteEnd))


Str.startsWith(self, prefix: Str) Bool:
    if self.len() < prefix.len():
        return Bool.False

    for i in range(u32(0), prefix.len()):
        if self._bytes.get(i) != prefix._bytes.get(i):
            return Bool.False

    Bool.True


Str.endsWith(self, suffix: Str) Bool:
    let suffixLen = suffix.len()
    let selfLen = self.len()

    if selfLen < suffixLen:
        return Bool.False

    for i in range(u32(0), suffixLen):
        if self._bytes.get(selfLen - suffixLen + i) != suffix._bytes.get(i):
            return Bool.False

    Bool.True


# Get the character at given byte index. Panics if the byte is not a first byte of a UTF-8
# code point.
Str.charAt(self, byteIndex: U32) Char:
    let byte = self._bytes.get(byteIndex)

    if byte < 128:
        return Char(_codePoint = byte.asU32())

    # Check continuation bit.
    if byte & 0b1100_0000 == 0b1000_0000:
        panic("Byte at index `byteIndex` is not a code point start")

    if byte & 0b1110_0000 == 0b1100_0000:
        # 2 bytes
        let b0 = (byte & 0b11111).asU32()
        let b1 = (self._bytes.get(byteIndex + 1) & 0b111111).asU32()
        Char(_codePoint = (b0 << 6) | b1)
    elif byte & 0b1111_0000 == 0b1110_0000:
        # 3 bytes
        let b0 = (byte & 0b1111).asU32()
        let b1 = (self._bytes.get(byteIndex + 1) & 0b111111).asU32()
        let b2 = (self._bytes.get(byteIndex + 2) & 0b111111).asU32()
        Char(_codePoint = (b0 << 12) | (b1 << 6) | b2)
    else:
        # 4 bytes
        let b0 = (byte & 0b111).asU32()
        let b1 = (self._bytes.get(byteIndex + 1) & 0b111111).asU32()
        let b2 = (self._bytes.get(byteIndex + 2) & 0b111111).asU32()
        let b3 = (self._bytes.get(byteIndex + 3) & 0b111111).asU32()
        Char(_codePoint = (b0 << 18) | (b1 << 12) | (b2 << 6) | b3)


Str.chars(self) CharIter:
    CharIter(_bytes = self._bytes, _idx = 0)


Str.charIndices(self) CharIndices:
    CharIndices(_str = self, _idx = 0)


Str.splitWhitespace(self) SplitWhitespace:
    SplitWhitespace(_str = self, _idx = 0)


Str.lines(self) Lines:
    Lines(_str = self, _idx = 0)


Str.trimAscii(self) Str:
    if self.isEmpty():
        return self

    let start: U32 = 0
    while start < self._bytes.len():
        if self._bytes.get(start).isAsciiWhitespace():
            start += 1
        else:
            break

    let end = self._bytes.len() - 1
    while end > start:
        if self._bytes.get(end).isAsciiWhitespace():
            end -= 1
        else:
            break

    self.substr(start, end + 1)


impl Eq[Str]:
    __eq(self: Str, other: Str) Bool:
        if self.len() != other.len():
            return Bool.False

        for i in range(u32(0), self.len()):
            if self._bytes.get(i) != other._bytes.get(i):
                return Bool.False

        Bool.True


impl Hash[Str]:
    hash(self: Str) U32:
        let hash: U32 = 2166136261
        for byte: U8 in self._bytes.iter():
            hash *= 16777619
            hash ^= byte.asU32()
        hash


impl ToStr[Str]:
    toStr(self: Str) Str:
        self


impl ToDoc[Str]:
    toDoc(self: Str) Doc:
        Doc.str("\"`self.toStr()`\"")


impl Clone[Str]:
    clone(self: Str) Str:
        self


type CharIter(
    # UTF-8 encoding of the string.
    _bytes: Array[U8],

    # Current index into `_bytes`.
    _idx: U32,
)


# Get the slice of the original string, starting from the current iteration point.
CharIter.asStr(self) Str:
    Str(_bytes = self._bytes.slice(self._idx, self._bytes.len()))


impl Iterator[CharIter, Char, exn]:
    next(self: CharIter) Option[Char] / exn:
        if self._idx == self._bytes.len():
            return Option.None

        let char = _charAt(self._bytes, self._idx)
        let charLength = char.lenUtf8()
        self._idx += charLength
        Option.Some(char)


type CharIndices(
    _str: Str,
    _idx: U32,
)


impl Iterator[CharIndices, (char: Char, idx: U32), exn]:
    next(self: CharIndices) Option[(char: Char, idx: U32)] / exn:
        if self._idx == self._str.len():
            return Option.None

        let char = self._str.charAt(self._idx)
        let charLength = char.lenUtf8()
        let idx = self._idx
        self._idx += charLength
        Option.Some((char = char, idx = idx))


_charAt(bytes: Array[U8], idx: U32) Char:
    let byte = bytes.get(idx)

    if byte < 128:
        return Char(_codePoint = byte.asU32())

    # Check continuation bit.
    if byte & 0b1100_0000 == 0b1000_0000:
        panic("Byte at index `idx` is not a code point start")

    if byte & 0b1110_0000 == 0b1100_0000:
        # 2 bytes
        let b0 = (byte & 0b11111).asU32()
        let b1 = (bytes.get(idx + 1) & 0b111111).asU32()
        Char(_codePoint = (b0 << 6) | b1)
    elif byte & 0b1111_0000 == 0b1110_0000:
        # 3 bytes
        let b0 = (byte & 0b1111).asU32()
        let b1 = (bytes.get(idx + 1) & 0b111111).asU32()
        let b2 = (bytes.get(idx + 2) & 0b111111).asU32()
        Char(_codePoint = (b0 << 12) | (b1 << 6) | b2)
    else:
        # 4 bytes
        let b0 = (byte & 0b111).asU32()
        let b1 = (bytes.get(idx + 1) & 0b111111).asU32()
        let b2 = (bytes.get(idx + 2) & 0b111111).asU32()
        let b3 = (bytes.get(idx + 3) & 0b111111).asU32()
        Char(_codePoint = (b0 << 18) | (b1 << 12) | (b2 << 6) | b3)


type SplitWhitespace(
    _str: Str,
    _idx: U32,
)


impl Iterator[SplitWhitespace, Str, exn]:
    next(self: SplitWhitespace) Option[Str] / exn:
        let wordStart = self._idx
        let wordEnd = wordStart
        let charIdxIter = self._str.substr(wordStart, self._str.len())
            .charIndices()

        # Skip initial whitespace, initialize `wordStart` and `wordEnd`.
        loop:
            let next: Option[(char: Char, idx: U32)] = charIdxIter.next()
            match next:
                Option.Some((char = char, idx = idx)):
                    if not char.isAsciiWhitespace():
                        wordStart = self._idx + idx
                        wordEnd = wordStart
                        break

                Option.None: return Option.None

        # Scan word, update `wordEnd`.
        loop:
            let next: Option[(char: Char, idx: U32)] = charIdxIter.next()
            match next:
                Option.Some((char = char, idx = idx)):
                    wordEnd = self._idx + idx
                    if char.isAsciiWhitespace():
                        break

                Option.None:
                    wordEnd += 1
                    break

        self._idx = wordEnd
        Option.Some(self._str.substr(wordStart, wordEnd))


type Lines(
    _str: Str,
    _idx: U32,
)


impl Iterator[Lines, Str, exn]:
    next(self: Lines) Option[Str] / exn:
        let lineStart = self._idx
        let charIdxIter = self._str.substr(lineStart, self._str.len())
            .charIndices()

        for (char = char, idx = idx): (char: Char, idx: U32) in charIdxIter:
            if char == '\n':
                let substr = self._str.substr(lineStart, self._idx + idx)

                # Continue with the next char
                self._idx += idx + 1

                return Option.Some(substr)

        let lineEnd = self._str.len()
        self._idx = lineEnd

        if lineStart == lineEnd:
            Option.None
        else:
            Option.Some(self._str.substr(lineStart, lineEnd))
