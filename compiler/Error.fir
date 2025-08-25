type Error(
    loc: Loc,
    msg: Str,
)

impl ToStr[Error]:
    toStr(self: Error) Str:
        "`self.loc.line + 1`:`self.loc.col + 1`: `self.msg`"

type AssertionError(
    msg: Str,
)

type Loc(
    file: Str,
    byteIdx: U32,
    byteLen: U32,
    line: U32,
    col: U32,
)

# TODO: Debug assert that `self.file == other.file`
Loc.combine(self, other: Loc) Loc:
    Loc(file = self.file,
        byteIdx = self.byteIdx,
        byteLen = other.byteIdx + other.byteLen - self.byteIdx,
        line = self.line,
        col = self.col)
