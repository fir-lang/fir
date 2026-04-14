main():
    let iter = [u32(1), u32(2)]
    for x: U32 in iter:
        print(x)

    let iter = ["a" = u32(1), "b" = u32(2)]
    for x: (key: Str, val: U32) in iter:
        print("`x.key` = `x.val`")

    # --------------------------------------------------------------------------
    # Type prefix in iters

    print("")

    let x: Vec[U32] = Vec.[]
    print(x)

    let x: Vec[Str] = Vec.["hi", "bye"]
    print(x)

    let x: Vec[Vec[Str]] = Vec.[Vec.["hi"], Vec.["bye"]]
    print(x)

    let x: Vec[Vec[U32]] = Vec.[
        Vec.[u32(1), u32(2), u32(3)],
        Vec.[u32(4), u32(5), u32(6)],
    ]
    print(x)

    let x: HashMap[Str, U32] = HashMap.[
        "a" = u32(1),
        "b" = u32(2),
    ]
    print(x)

    # --------------------------------------------------------------------------
    # Without type prefix at the outer levels

    print("")

    let x: Vec[U32] = []
    print(x)

    let x: Vec[Str] = ["hi", "bye"]
    print(x)

    let x: Vec[Vec[Str]] = [Vec.["hi"], Vec.["bye"]]
    print(x)

    let x: Vec[Vec[U32]] = [
        Vec.[u32(1), u32(2), u32(3)],
        Vec.[u32(4), u32(5), u32(6)],
    ]
    print(x)

    let x: HashMap[Str, U32] = [
        "a" = u32(1),
        "b" = u32(2),
    ]
    print(x)

# expected stdout:
# 1
# 2
# a = 1
# b = 2
# 
# []
# [hi,bye]
# [[hi],[bye]]
# [[1,2,3],[4,5,6]]
# {b: 2, a: 1}
# 
# []
# [hi,bye]
# [[hi],[bye]]
# [[1,2,3],[4,5,6]]
# {b: 2, a: 1}
