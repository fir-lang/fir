# This is generated file, do not edit.

import [
    Compiler/Token,
    Tool/Peg/ParseTree,
    Tool/Peg/TestState,
]


abcs(state: ParserState[Token, UserState]) () / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            abc(state)
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let symResult = try(\(): abc(state))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let val = do:
                ()
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


abc(state: ParserState[Token, UserState]) () / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                state.state().a += 1
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "b", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                state.state().b += 1
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "c", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                state.state().c += 1
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))
