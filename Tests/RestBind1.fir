mkRecord() (x: U32, y: U32, msg: Str):
    (x = u32(1), y = u32(2), msg = "hi")

main():
    let (x, ..rest) = mkRecord()
    print(x)
    print(rest.msg)
    print(rest.y)

    let (x, y, ..rest2) = mkRecord()
    print(x)
    print(y)
    print(rest2.msg)

    let (msg, ..rest3) = mkRecord()
    print(msg)
    print(rest3.x)
    print(rest3.y)

# expected stdout:
# 1
# hi
# 2
# 1
# 2
# hi
# hi
# 1
# 2
