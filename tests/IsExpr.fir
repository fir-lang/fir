main():
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

    if x is Option.None and y is Option.Some(a):
        print(a)

    if x is Option.None and y is Option.Some(a) and a.mod(2) == 0:
        print(a)
    else:
        print("NO")

    if x is Option.None and y is Option.Some(a) and a.mod(2) != 0:
        print(a)

    if x is Option.None | Option.None or x is Option.Some(_):
        print("YES")

    let res: Result[U32, U32] = Result.Ok(456)
    if res is Result.Ok(a) | Result.Err(a):
        print(a)

    if res is Result.Ok(a) | Result.Err(a) and a.mod(2) == 0:
        print(a)

    if res is Result.Err(a) | Result.Ok(a) and a.mod(2) == 0:
        print(a)

# expected stdout:
# NA
# NA
# NA
# 123
# 123
# NO
# 123
# YES
# 456
# 456
# 456
