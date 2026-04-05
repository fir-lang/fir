# This is generated file, do not edit.

import [
    Compiler/Interpolation2,
    Compiler/ParseUtils2,
    Compiler/Token,
    Tool/Peg/ParseTree,
]


justTesting[AstExts[exts], AstIds[AstExts[exts].Ids],](
    state: ParserState[Token, ()],
) Expr[exts] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let cur = state.nextCursor()
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Expr.Var(VarExpr(id = newVarId(cur), userTyArgs = Option.None))
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))
