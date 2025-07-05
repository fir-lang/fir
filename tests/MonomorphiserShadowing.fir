type E1:
    E1

type E2:
    E2

a(f1: Fn() () / [..errs]) () / [..errs]:
    f1()

f1() () / [E1, ..r]:
    throw(~E1.E1)

main():
    match try(||: a(f1)):
        Result.Ok(()): ()
        Result.Err(~E1.E1): printStr("E1 caught")
        Result.Err(~E2.E2): printStr("E2 caught")

# expected stdout: E1 caught

# expected stderr: tests/MonomorphiserShadowing.fir:14:5: Unexhaustive pattern match
