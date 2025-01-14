fn f1[r]() {E1(i: I32), ..r}
    throw(~E1(i = 123))

fn main()
    match try(f1):
        Result.Err(~E1(i)): printStr("i = `i.toStr()`")
        Result.Ok(()): panic("")
