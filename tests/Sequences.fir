main():
    let iter = [1u32, 2u32]
    for x: U32 in iter:
        print(x)

    let iter = ["a" = 1u32, "b" = 2u32]
    for x: (key: Str, value: U32) in iter:
        print("`x.key` = `x.value`")

    let x: Vec[U32] = Vec.[]
    print(x)

    let x: Vec[Str] = Vec.["hi", "bye"]
    print(x)

# expected stdout:
# 1
# 2
# a = 1
# b = 2
# []
# [hi,bye]
