fn f1(): {E1, ..r}
    throw(~E1)

fn f2(): {E2, ..r}
    untry(Result.Err(~E2))

fn main()
    match try(f1):
        Result.Err(~E1): printStr("OK")
        Result.Ok(()): panic("")

# expected stdout:
# tests/Exn1.fir:8:5: Unexhaustive pattern match
# OK
