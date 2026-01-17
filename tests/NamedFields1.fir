type Result[t, e]:
    Ok(val: t)
    Err(val: e)

prim type I32

prim type Str

trait ToStr[t]:
    toStr(self: t) Str

impl ToStr[I32]:
    prim toStr(self: I32) Str

resultToString(result: Result[I32, I32]) Str:
    match result:
        Result.Ok(val = v):
            "Ok(`v`)"
        Result.Err(val = v):
            "Err(`v`)"

# args: --typecheck --no-prelude
