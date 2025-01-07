fn main()
    let f = Vec.len

    let vec1 = Vec.withCapacity(10u32)
    vec1.push("a")
    vec1.push("b")

    let vec2 = Vec.withCapacity(20u32)
    vec2.push(123i32)

    printStr(f(vec1).toStr())
    printStr(f(vec2).toStr())

# args: --no-backtrace
# expected stderr: tests/TcFail3.fir:12:16: Unable to unify types I32 and Str
