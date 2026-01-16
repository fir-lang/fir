main():
    let x: Array[U8] = Array.fromIter(range(u8(0), u8(10)), 10)
    x.copyWithin(5, 0, 5)
    print(x)

    let x: Array[U32] = Array.fromIter(range(u32(0), u32(10)), 10)
    x.copyWithin(5, 0, 5)
    print(x)

    let x: Array[U64] = Array.fromIter(range(u64(0), u64(10)), 10)
    x.copyWithin(5, 0, 5)
    print(x)

# expected stdout:
# [5,6,7,8,9,5,6,7,8,9]
# [5,6,7,8,9,5,6,7,8,9]
# [5,6,7,8,9,5,6,7,8,9]
