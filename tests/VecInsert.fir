main():
    let v: Vec[U32] = Vec.[u32(1), u32(2), u32(3), u32(4), u32(5), u32(6), u32(7)]
    v.insert(0, 10)
    print(v)

    v.insert(v.len() / 2, 99)
    print(v)

    v.insert(v.len(), 11)
    print(v)

# expected stdout:
# [10,1,2,3,4,5,6,7]
# [10,1,2,3,99,4,5,6,7]
# [10,1,2,3,99,4,5,6,7,11]
