import [Compiler/Error]


#[derive(ToDoc)]
type TypeError(
    loc: Loc,
    msg: Str,
)
