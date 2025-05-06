main
    let x: Option[U32] = Option.None
    if x is Option.None:
        print("NA")

    let y: Option[U32] = Option.Some(123)
    if y is Option.Some(a):
        print(a)

    if x is Option.None && y is Option.Some(a):
        print(a)

# expected stdout:
# NA
# 123
# 123
