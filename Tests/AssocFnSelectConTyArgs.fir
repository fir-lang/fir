main():
    let v1 = Vec[U32].withCapacity(10)
    print(v1)

    let v1_2 = Vec[U32].withCapacity(10)
    v1_2.push(u32(123))
    print(v1_2)

    let v2 = Vec.withCapacity[U32, []](10)
    print(v2)

    let v2_2 = Vec.withCapacity[U32, []](10)
    v2_2.push(u32(123))
    print(v2_2)

    let v3 = Vec[U32].withCapacity[U32, []](10)
    print(v3)

    let v3_2 = Vec[U32].withCapacity[U32, []](10)
    v3_2.push(u32(123))
    print(v3_2)

# expected stdout:
# []
# [123]
# []
# [123]
# []
# [123]
