main
    let v: Vec[(x: U32, y: U32)] = Vec.withCapacity(10)
    v.push((x = 1, y = 2))
    v.push((x = 3, y = 4))
    v.push((x = 5, y = 6))
    for (x = x, y = y): (x: U32, y: U32) in v.iter():
        printStr("x = `x.toStr()`, y = `y.toStr()`")

# expected stdout:
# x = 1, y = 2
# x = 3, y = 4
# x = 5, y = 6
