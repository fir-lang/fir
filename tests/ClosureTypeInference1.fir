main()
    let x: Option[U32] = Option.Some(123u32)
    print(x.map(fn(i) { i + 10 }))
    print(x.map(fn(i) { i.toStr() }))
    print(x.map(fn(i) { i.toStr() }).unwrapOr("wat"))
    print(try({
        x.map(fn(i) {
            if Bool.False:
                return 123u32
            throw("Hi")
        })
    }))
    print(x.guard(fn(i) { i != 0 }))

# expected stdout:
# Option.Some(133)
# Option.Some(123)
# 123
# Result.Err(Hi)
# Option.Some(123)
