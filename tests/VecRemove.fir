main():
    let v: Vec[U32] = Vec.[u32(1), u32(2), u32(3), u32(4), u32(5), u32(6), u32(7)]
    print(v.remove(0))
    print(v)

    print(v.remove(v.len() - 1))
    print(v)

    print(v.remove(v.len() / 2))
    print(v)

# expected stdout:
# 1
# [2,3,4,5,6,7]
# 7
# [2,3,4,5,6]
# 4
# [2,3,5,6]
