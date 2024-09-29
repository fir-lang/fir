# TODO: We may want to allow unnamed fields: `type Char(U32)`.
type Char:
    _codePoint: U32

impl Eq for Char:
    fn __eq(self, other: Char): Bool =
        self._codePoint == other._codePoint

impl Char:
    fn fromU32(codePoint: U32): Option[Char] =
        if codePoint >= 0x110000 || (codePoint >= 0xD800 && codePoint <= 0xDFFF):
            return Option.None

        Option.Some(Char(_codePoint = codePoint))

    fn lenUtf8(self): U32 =
        if self._codePoint < 0x80:
            1
        elif self._codePoint < 0x800:
            2
        elif self._codePoint < 0x10000:
            3
        else:
            4

impl ToStr for Char:
    fn toStr(self): Str =
        let strBuf = StrBuf.withCapacity(self.lenUtf8() + 2)
        strBuf.push('\'')
        strBuf.push(self)
        strBuf.push('\'')
        strBuf.toStr()      # TODO: This copies the array, maybe add an internal version that doesn't
