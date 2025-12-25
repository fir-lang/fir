import [Compiler/Ast]


strParts(interpolations: Vec[(expr: Expr, end: Token)], end: Token) Vec[StrPart]:
    panic("TODO")


copyUpdateEscapes(s: Str) Str:
    let ret = StrBuf.withCapacity(s.len())
    panic("TODO")
