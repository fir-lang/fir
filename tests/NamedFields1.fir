type Result[T, E]:
    Ok:
        value: T

    Err:
        value: E

prim type I32

prim type Str

impl I32:
    prim fn toStr(self): Str

fn resultToString(result: Result[I32, I32]): Str =
    match result:
        Result.Ok(value = v):
            "Ok(`v.toStr()`)"
        Result.Err(value = v):
            "Err(`v.toStr()`)"

# args: --typecheck --no-prelude
