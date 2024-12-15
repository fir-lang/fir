fn main() =
    for i in irange(0u32, 5):
        test(i)

fn test(len: U32) =
    let vec = Vec.withCapacity(len)
    for i in range(0u32, len):
        vec.push(len - i)
    vec.sort()
    printStr(vec.toStr())

# expected stdout:
# []
# [1]
# [1,2]
# [1,2,3]
# [1,2,3,4]
# [1,2,3,4,5]
