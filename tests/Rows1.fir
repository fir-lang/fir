fn test[R](r: (x: I32, y: I32 | R)) =
    printStr(r.x.toStr())
    printStr(r.y.toStr())

fn id[R](r: (x: I32 | R)): (x: I32 | R) =
    printStr(r.x.toStr())
    r

fn main() =
    test(id((x = 1, y = 2)))
    test(id((x = 3, y = 4, z = "hi")))

# expected stdout:
# 1
# 1
# 2
# 3
# 3
# 4
