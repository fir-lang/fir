main():
    let x: Option[U32] = Option.Some(u32(123))
    print(x.map(|i|: i + 10))
    print(x.map(|i|: i.toStr()))
    print(x.map(|i|: i.toStr()).unwrapOr("wat"))
    print(try(||:
        x.map(|i|:
            if Bool.False:
                return u32(123)
            throw("Hi"))))
    print(x.guard(|i|: i != 0))

# expected stdout:
# Option.Some(133)
# Option.Some(123)
# 123
# Result.Err(Hi)
# Option.Some(123)
