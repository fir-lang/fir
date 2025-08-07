type StrBuf(
    # UTF-8 encoding of the string.
    _bytes: Vec[U8],
)

StrBuf.withCapacity(cap: U32) StrBuf:
    StrBuf(_bytes = Vec.withCapacity(cap))

StrBuf.len(self) U32:
    self._bytes.len()

StrBuf.clear(self):
    self._bytes.clear()

StrBuf.push(self, char: Char):
    let code = char._codePoint
    let len = char.lenUtf8()
    if len == 1:
        self._bytes.push(code.asU8())
    elif len == 2:
        let b0 = ((code >> 6) & 0x1F).asU8() | 0b1100_0000
        let b1 = (code & 0x3F).asU8() | 0b1000_0000
        self._bytes.push(b0)
        self._bytes.push(b1)
    elif len == 3:
        let b0 = ((code >> 12) & 0x0F).asU8() | 0b1110_0000
        let b1 = ((code >> 6) & 0x3F).asU8() | 0b1000_0000
        let b2 = (code & 0x3F).asU8() | 0b1000_0000
        self._bytes.push(b0)
        self._bytes.push(b1)
        self._bytes.push(b2)
    else:
        let b0 = ((code >> 18) & 0x07).asU8() | 0b1111_0000
        let b1 = ((code >> 12) & 0x3F).asU8() | 0b1000_0000
        let b2 = ((code >> 6) & 0x3F).asU8() | 0b1000_0000
        let b3 = (code & 0x3F).asU8() | 0b1000_0000
        self._bytes.push(b0)
        self._bytes.push(b1)
        self._bytes.push(b2)
        self._bytes.push(b3)

StrBuf.pushStr(self, str: Str):
    # TODO: Maybe consider memcpy-ing the bytes.
    self._bytes.reserve(str.len())
    for char: Char in str.chars():
        self.push(char)

impl ToStr[StrBuf]:
    toStr(self: StrBuf) Str:
        Str.fromUtf8Vec(self._bytes)
