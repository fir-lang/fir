fn f1(): {E1, ..r}
    throw(~E1)

fn f2(): {E2, ..r}
    untry(Result.Err(~E2))

fn f3(): {E1, E2, ..r}
    f1()
    f2()

fn main()
    match try(f1):
        Result.Err(~E1): printStr("OK")
        Result.Ok(()): panic("")

    match try(f3):
        Result.Err(~E1): printStr("OK")
        Result.Err(~E2): panic("1")
        Result.Ok(()): panic("2")

# expected stdout:
# tests/Exn1.fir:12:5: Unexhaustive pattern match
# tests/Exn1.fir:16:5: Unexhaustive pattern match
# OK
# OK
