type Result[t, e]:
    Ok:
        value: t

    Err:
        value: e

prim type I32

prim type Str

trait ToStr[t]:
    fn toStr(self): Str

impl ToStr for I32:
    prim fn toStr(self): Str

fn resultToString(result: Result[I32, I32]): Str =
    match result:
        Result.Ok(value = v):
            "Ok(`v`)"
        Result.Err(value = v):
            "Err(`v`)"

# args: --typecheck --no-prelude
