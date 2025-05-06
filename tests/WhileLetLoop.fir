main
    let v: Vec[U32] = Vec.withCapacity(10)
    v.push(123u32)
    v.push(456u32)
    v.push(789u32)

    let iter = v.iter()
    let next: Fn(): [] Option[U32] = iter.next
    while next() is Option.Some(next):
        printStr(next.toStr())

# expected stdout:
# 123
# 456
# 789
