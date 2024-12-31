fn test[R](r: (x: I32, y: I32, ..R)) =
    printStr(r.x.toStr())
    printStr(r.y.toStr())

fn id[R](r: (x: I32, ..R)): (x: I32, ..R) =
    printStr(r.x.toStr())
    r

type Test[R]:
    x: (x: I32, ..R)

fn main() =
    test(id((x = 1, y = 2)))
    test(id((x = 3, y = 4, z = "hi")))
    let struct = Test(x = (x = 123, y = 456))
    test(id(struct.x))

# expected stdout:
# 1
# 1
# 2
# 3
# 3
# 4
# 123
# 123
# 456
