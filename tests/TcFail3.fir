fn main(input: Str) =
    let f = Vec.len

    let vec1 = Vec.withCapacity(10)
    vec1.push("a")
    vec1.push("b")

    let vec2 = Vec.withCapacity(20)
    vec2.push(123i32)

    printStr(f(vec1).toStr())
    printStr(f(vec2).toStr())

# args: --no-backtrace
# expected stderr: Unable to unify types I32 and Str at tests/TcFail3.fir:12:16
