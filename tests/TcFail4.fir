fn main(input: Str) =
    let f = Vec.withCapacity

    let vec1 = f(10)
    vec1.push("a")
    vec1.push("b")

    let vec2 = f(20)
    vec2.push(123i32)

# args: --no-backtrace
# expected stderr: Unable to unify types I32 and Str at tests/TcFail4.fir:9:15
