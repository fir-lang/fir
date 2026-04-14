main():
    let v: Vec[U32] = Vec.fromIter(range(u32(0), u32(1000)).take(10))
    print(v)

    let v: Vec[U32] = Vec.fromIter(range(u32(0), u32(1000)).take(0))
    print(v)

    let v: Vec[U32] = Vec.fromIter(range(u32(0), u32(10)).take(1000))
    print(v)


# expected stdout:
# [0,1,2,3,4,5,6,7,8,9]
# []
# [0,1,2,3,4,5,6,7,8,9]
