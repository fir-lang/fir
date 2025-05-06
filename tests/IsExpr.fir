main
    let x: Option[U32] = Option.None

    if x is Option.None:
        print("NA")

    if !(x is Option.Some(_)):
        print("NA")

    if !(x is Option.Some(a)):
        print("NA")

    let y: Option[U32] = Option.Some(123)
    if y is Option.Some(a):
        print(a)

    if x is Option.None && y is Option.Some(a):
        print(a)

    if x is Option.None && y is Option.Some(a) && a.mod(2) == 0:
        print(a)
    else:
        print("NO")

    if x is Option.None && y is Option.Some(a) && a.mod(2) != 0:
        print(a)

    if x is Option.None | Option.None || x is Option.Some(_):
        print("YES")

# expected stdout:
# NA
# NA
# NA
# 123
# 123
# NO
# 123
# YES
