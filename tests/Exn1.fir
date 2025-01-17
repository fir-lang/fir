f1(): {E1, ..r}
    throw(~E1)

f2(): {E2, ..r}
    untry(Result.Err(~E2))

f3(): {E1, E2, ..r}
    f1()
    f2()

forEach(vec: Vec[t], f: Fn(t): {..r}): {..r}
    for t in vec.iter():
        f(t)

throwOnOdd(i: U32): {OddNumberError(i: U32), ..r}
    if i & 1 == 0:
        throw(~OddNumberError(i = i))

forEachWithControlFlow(vec: Vec[t], f: Fn(t): {Break, ..r}): {..r} Result[[..r], ()]
    for t in vec.iter():

        match try(fn(): {Break, ..r} { f(t) }):
            Result.Err(~Break): break
            Result.Err(other): return Result.Err(other)
            Result.Ok(()): ()

    Result.Ok(())

main()
    match try(f1):
        Result.Err(~E1): printStr("OK")
        Result.Ok(()): panic("")

    match try(f3):
        Result.Err(~E1): printStr("OK")
        Result.Err(~E2): panic("1")
        Result.Ok(()): panic("2")

    let vec: Vec[U32] = Vec.withCapacity(3)
    vec.push(1)
    vec.push(2)
    vec.push(3)

    match try(fn(): {OddNumberError(i: U32)} () {
        let vec: Vec[U32] = Vec.withCapacity(3)
        vec.push(1)
        vec.push(2)
        vec.push(3)
        forEach(vec, throwOnOdd)
    }):
        Result.Err(~OddNumberError(i = i)): printStr("Odd number: `i.toStr()`")
        Result.Ok(()): ()

# expected stdout:
# tests/Exn1.fir:29:5: Unexhaustive pattern match
# tests/Exn1.fir:33:5: Unexhaustive pattern match
# OK
# OK
# Odd number: 2
