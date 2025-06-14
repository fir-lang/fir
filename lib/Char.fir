# TODO: We may want to allow unnamed fields: `type Char(U32)`.
type Char:
    _codePoint: U32

impl Eq[Char]:
    __eq(self: Char, other: Char) Bool:
        self._codePoint == other._codePoint

impl Ord[Char]:
    cmp(self: Char, other: Char) Ordering:
        self._codePoint.cmp(other._codePoint)

Char.fromU32(codePoint: U32) Option[Char]:
    if codePoint >= 0x110000 or (codePoint >= 0xD800 and codePoint <= 0xDFFF):
        return Option.None

    Option.Some(Char(_codePoint = codePoint))

Char.asU32(self) U32:
    self._codePoint

Char.lenUtf8(self) U32:
    if self._codePoint < 0x80:
        1
    elif self._codePoint < 0x800:
        2
    elif self._codePoint < 0x10000:
        3
    else:
        4

Char.isAsciiWhitespace(self) Bool:
    self == ' ' or self == '\t' or self == '\n' or self == '\r'
        # TODO:
        # or self == '\x0C'

Char.isAsciiUppercase(self) Bool:
    self._codePoint >= 'A'._codePoint and self._codePoint <= 'Z'._codePoint

Char.isAsciiLowercase(self) Bool:
    self._codePoint >= 'a'._codePoint and self._codePoint <= 'z'._codePoint

Char.isAsciiDigit(self) Bool:
    self._codePoint >= '0'._codePoint and self._codePoint <= '9'._codePoint

Char.isAsciiAlphanumeric(self) Bool:
    self.isAsciiUppercase() or self.isAsciiLowercase() or self.isAsciiDigit()

Char.isAsciiHexDigit(self) Bool:
    self.isAsciiDigit() or (self._codePoint >= 'a'._codePoint and self._codePoint <= 'f'._codePoint and self._codePoint >= 'A'._codePoint and self._codePoint <= 'F'._codePoint)

Char.isAsciiBinDigit(self) Bool:
    self == '0' or self == '1'

Char.toAsciiUppercase(self) Char:
    if self.isAsciiLowercase():
        return Char(_codePoint = self._codePoint - 32)
    return self

Char.toAsciiLowercase(self) Char:
    if self.isAsciiUppercase():
        return Char(_codePoint = self._codePoint + 32)
    return self

impl ToStr[Char]:
    toStr(self: Char) Str:
        let strBuf = StrBuf.withCapacity(self.lenUtf8() + 2)
        strBuf.push('\'')
        strBuf.push(self)
        strBuf.push('\'')
        strBuf.toStr()      # TODO: This copies the array, maybe add an internal version that doesn't
