main
    let x: Option[U32] = Option.Some(123)

    if x is Option.Some(x):
        print(x)
        x = 999
        print(x)

    print(x)

    let y: Result[U32, U32] = Result.Ok(456)

    if y is Result.Ok(y) | Result.Err(y):
        print(y)
        y = 999
        print(y)

    print(y)

# expected stdout:
# 123
# 999
# Option.Some(123)
# 456
# 999
# Result.Ok(456)
