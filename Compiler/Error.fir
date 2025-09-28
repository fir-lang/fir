type Error(
    loc: Loc,
    msg: Str,
)


impl ToStr[Error]:
    toStr(self: Error) Str:
        "`self.loc.file`:`self.loc.line + 1`:`self.loc.col + 1`: `self.msg`"


type Loc(
    file: Str,
    line: U32,
    col: U32,
)
