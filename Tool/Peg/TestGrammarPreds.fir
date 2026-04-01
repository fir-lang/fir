# This is generated file, do not edit.

import [
    Compiler/Token,
    Tool/Peg/ParseTree,
    Tool/Peg/PredTests,
]


items[ItemExts[t],](state: ParserState[Token, ()]) Vec[Item[t]] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            let items = Vec.empty()
            items.push(item(state))
            let zeroOrMoreCursor0 = state._cursor
            loop:
                let itemsLen0 = items.len()
                let symResult = try(\(): items.push(item(state)))
                match symResult:
                    Result.Err(err):
                        state._cursor = zeroOrMoreCursor0
                        items.truncate(itemsLen0)
                        break
                    Result.Ok(ok): zeroOrMoreCursor0 = state._cursor
            let val = do:
                items
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))


item[ItemExts[t],](state: ParserState[Token, ()]) Item[t] / U32:
    let cursor0 = state._cursor
    let altResult = try(
        \():
            if state.peek() is Option.Some(sym)
                    and sym is Token(kind = TokenKind.LowerId, text = "a", ..):
                state._cursor += 1
            else:
                throw(state.updateErrorCursor(state._cursor))
            let val = do:
                Item.A(x = 0, ..ItemExts[t].defaultA())
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
                Item.B(msg = "hi", ..ItemExts[t].defaultB())
            val,
    )
    match altResult:
        Result.Err(err): state._cursor = cursor0
        Result.Ok(val): return val
    throw(state.updateErrorCursor(state._cursor))
