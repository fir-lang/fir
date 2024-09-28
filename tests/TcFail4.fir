fn main() =
    let f = Vec.withCapacity

    let vec1 = f(10u32)
    vec1.push("a")
    vec1.push("b")

    let vec2 = f(20u32)
    vec2.push(123i32)

# args: --no-backtrace
# expected stderr: tests/TcFail4.fir:9:15: Unable to unify types I32 and Str
