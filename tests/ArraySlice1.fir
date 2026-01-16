main():
    let x: Array[U8] = Array.fromIter([u8(0), u8(1), u8(2)], 3)
    print("U8:")
    print(x)
    for start in range(u32(0), u32(4)):
        for end in range(start, u32(4)):
            print(x.slice(start, end))

    let x: Array[U32] = Array.fromIter([u32(0), u32(1), u32(2)], 3)
    print("U32:")
    print(x)
    for start in range(u32(0), u32(4)):
        for end in range(start, u32(4)):
            print(x.slice(start, end))

    let x: Array[U64] = Array.fromIter([u64(0), u64(1), u64(2)], 3)
    print("U64:")
    print(x)
    for start in range(u32(0), u32(4)):
        for end in range(start, u32(4)):
            print(x.slice(start, end))

# expected stdout:
# U8:
# [0,1,2]
# []
# [0]
# [0,1]
# [0,1,2]
# []
# [1]
# [1,2]
# []
# [2]
# []
# U32:
# [0,1,2]
# []
# [0]
# [0,1]
# [0,1,2]
# []
# [1]
# [1,2]
# []
# [2]
# []
# U64:
# [0,1,2]
# []
# [0]
# [0,1]
# [0,1,2]
# []
# [1]
# [1,2]
# []
# [2]
# []
