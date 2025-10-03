main():
    let f = Vec.withCapacity

    let vec1 = f(u32(10))
    vec1.push("a")
    vec1.push("b")

    let vec2 = f(u32(20))
    vec2.push(i32(123))

# expected stderr: tests/TcFail4.fir:9:15: Unable to unify types I32 and Str
