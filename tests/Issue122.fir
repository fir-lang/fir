main():
    let x: Option[U32] = Option.Some(123)
    let bool = x is Option.Some(x)
    print(x)

# expected stdout: Option.Some(123)
