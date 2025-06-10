type E1:
    E1

type E2:
    E2

f1() () / [E1, ..r]:
    throw(~E1.E1)

f2() () / [E2, ..r]:
    untry(Result.Err(~E2.E2))

f3() () / [E1, E2, ..r]:
    f1()
    f2()

forEach(vec: Vec[t], f: Fn(t) () / [..r]) () / [..r]:
    for t in vec.iter():
        f(t)

type OddNumberError:
    i: U32

throwOnOdd(i: U32) () / [OddNumberError, ..r]:
    if i & 1 == 0:
        throw(~OddNumberError(i = i))

type Break:
    Break

forEachWithControlFlow(vec: Vec[t], f: Fn(t) () / [Break, ..r]) Result[[..r], ()] / [..r]:
    for t in vec.iter():
        match try(fn() () / [Break, ..r] { f(t) }):
            Result.Err(~Break.Break): break
            Result.Err(other): return Result.Err(other)
            Result.Ok(()): ()

    Result.Ok(())

main():
    match try(f1):
        Result.Err(~E1.E1): printStr("OK")
        Result.Ok(()): panic("")

    match try(f3):
        Result.Err(~E1.E1): printStr("OK")
        Result.Err(~E2.E2): panic("1")
        Result.Ok(()): panic("2")

    let vec: Vec[U32] = Vec.withCapacity(3)
    vec.push(1)
    vec.push(2)
    vec.push(3)

    match try(fn() () / [OddNumberError] { forEach(vec, throwOnOdd) }):
        Result.Err(~OddNumberError(i = i)): printStr("Odd number: `i.toStr()`")
        Result.Ok(()): ()

    printStr("---")

    forEachWithControlFlow(vec, fn(i: U32) () / [Break] {
        printStr(i.toStr())
    })

    printStr("---")

    forEachWithControlFlow(vec, fn(i: U32) () / [Break] {
        printStr(i.toStr())
        if i & 0b1 == 0:
            throw(~Break.Break)
    })

    ()

# expected stdout:
# OK
# OK
# Odd number: 2
# ---
# 1
# 2
# 3
# ---
# 1
# 2

# expected stderr:
# tests/Exn1.fir:41:5: Unexhaustive pattern match
# tests/Exn1.fir:45:5: Unexhaustive pattern match

