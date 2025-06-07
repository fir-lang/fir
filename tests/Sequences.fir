main():
    let iter = [1u32, 2u32]
    for x: U32 in iter:
        print(x)

    let iter = ["a" = 1u32, "b" = 2u32]
    for x: (key: Str, value: U32) in iter:
        print("`x.key` = `x.value`")

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
        Vec.[1u32, 2u32, 3u32],
        Vec.[4u32, 5u32, 6u32],
    ]
    print(x)

    let x: HashMap[Str, U32] = HashMap.[
        "a" = 1u32,
        "b" = 2u32,
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
        Vec.[1u32, 2u32, 3u32],
        Vec.[4u32, 5u32, 6u32],
    ]
    print(x)

    let x: HashMap[Str, U32] = [
        "a" = 1u32,
        "b" = 2u32,
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
