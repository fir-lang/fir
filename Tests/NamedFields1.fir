#[NoImplicitPrelude]
import []

type Result[t, e]:
    Ok(val: t)
    Err(val: e)

type Type1

resultToVal(result: Result[Type1, Type1]) Type1:
    match result:
        Result.Ok(val = v):
            v
        Result.Err(val = v):
            v

# args: --typecheck
