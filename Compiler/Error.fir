type Error(
    loc: Loc,
    msg: Str,
)


impl ToStr[Error]:
    toStr(self: Error) Str:
        "`self.loc.file`:`self.loc.line + 1`:`self.loc.col + 1`: `self.msg`"


#[derive(ToDoc)]
type Loc(
    file: Str,
    line: U32,
    col: U32,
)


impl ToStr[Loc]:
    toStr(self: Loc) Str:
        "`self.file`:`self.line + 1`:`self.col + 1`"


impl ToDoc[Loc]:
    toDoc(self: Loc) Doc:
        panic("TODO")
