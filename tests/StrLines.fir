collect(iter: Lines): Vec[Str]
    let vec = Vec.withCapacity(10)
    for a: Str in iter:
        vec.push(a)
    vec

main
    let s = ""
    printStr(collect("".lines()).toStr())
    printStr(collect("a".lines()).toStr())
    printStr(collect("a\n".lines()).toStr())
    printStr(collect("\na\n".lines()).toStr())
    printStr(collect("\n\n\n".lines()).toStr())
    printStr(collect("\n\n\na".lines()).toStr())

# expected stdout:
# []
# [a]
# [a]
# [,a]
# [,,]
# [,,,a]
