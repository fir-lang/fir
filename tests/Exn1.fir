fn f1(): {E1, ..r}
    throw(~E1)

fn f2(): {E2, ..r}
    untry(Result.Err(~E2))

fn f3(): {E1, E2, ..r}
    f1()
    f2()

fn forEach(vec: Vec[t], f: Fn(t): {..r}): {..r}
    for i in range(0u32, vec.len()):
        f(vec.get(i))

fn throwOnOdd(i: U32): {OddNumberError(i: U32), ..r}
    if i & 1 == 0:
        throw(~OddNumberError(i = i))

# Implement closures and inline this function.
fn f4(): {OddNumberError(i: U32), ..r}
    let vec: Vec[U32] = Vec.withCapacity(3)
    vec.push(1)
    vec.push(2)
    vec.push(3)
    forEach(vec, throwOnOdd)

#|
TODO: Implement closures
fn forEachWithControlFlow(vec: Vec[t], f: Fn(t): {Break, ..r}): {..r}
    for i in range(0u32, vec.len()):
        match try({ f(vec.get(i)) }):
            Result.Err(~Break): break
            Result.Err(other): return Result.Err(other)
            Result.OK(()): ()
|#

fn main()
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

    match try(f4):
        Result.Err(~OddNumberError(i = i)): printStr("Odd number: `i.toStr()`")
        Result.Ok(()): ()

# expected stdout:
# tests/Exn1.fir:38:5: Unexhaustive pattern match
# tests/Exn1.fir:42:5: Unexhaustive pattern match
# tests/Exn1.fir:52:5: Unexhaustive pattern match
# OK
# OK
# Odd number: 2
