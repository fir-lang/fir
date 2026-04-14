main():
    let v: Vec[U32] = Vec.[u32(1), u32(2), u32(3), u32(4)]
    print(v)
    print(v.len())

    let a = v.takeArray()
    print(v)
    print(v.len())

    print(a)
    print(a.len())

    v.push(5)
    a.set(0, 100)
    print(v)
    print(a)

# expected stdout:
# [1,2,3,4]
# 4
# []
# 0
# [1,2,3,4]
# 4
# [5]
# [100,2,3,4]
