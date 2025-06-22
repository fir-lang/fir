main():
    let v: Vec[U32] = Vec.withCapacity(10)
    v.push(u32(123))
    v.push(u32(456))
    v.push(u32(789))

    let iter = v.iter()
    let next: Fn() Option[U32] / [] = iter.next
    while next() is Option.Some(next):
        printStr(next.toStr())

# expected stdout:
# 123
# 456
# 789
