fn f1[r]() {E1, ..r}
    throw(~E1)

fn main()
    match try(f1):
        Result.Err(~E1): printStr("OK")
        Result.Ok(()): panic("")
