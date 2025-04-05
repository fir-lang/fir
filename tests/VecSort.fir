main()
    for i: U32 in irange(0u32, 5):
        test(i)

test(len: U32)
    let vec = Vec.withCapacity(len)
    for i: U32 in range(0u32, len):
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
