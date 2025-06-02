main():
    let x: Option[U32] = Option.Some(0)
    while x is Option.Some(x1):
        print(x1)
        if x1 == 10:
            x = Option.None
        else:
            x = Option.Some(x1 + 1)

# expected stdout:
# 0
# 1
# 2
# 3
# 4
# 5
# 6
# 7
# 8
# 9
# 10
