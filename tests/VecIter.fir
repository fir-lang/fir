main()
    let vec: Vec[U32] = Vec.withCapacity(10)
    vec.push(1)
    vec.push(2)
    vec.push(3)
    for i: U32 in vec.iter():
        printStr(i.toStr())
        printStr(vec.pop().toStr())

# expected stdout:
# 1
# Option.Some(3)
# 2
# Option.Some(2)
