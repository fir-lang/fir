a(f1: Fn(): {..errs} ()): {..errs} ()
    f1()

f1(): {E1, ..r} ()
    throw(~E1)

main
    match try({ a(f1) }):
        Result.Ok(()): ()
        Result.Err(~E1): printStr("E1 caught")
        Result.Err(~E2): printStr("E2 caught")

# expected stdout:
# tests/Issue81.fir:8:5: Unexhaustive pattern match
# E1 caught
