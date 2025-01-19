collect[i: Iterator[Item = a], a](iter: i): Vec[a]
    let vec = Vec.withCapacity(10)
    for a in iter:
        vec.push(a)
    vec

main
    printStr(collect("".splitWhitespace()).toStr())
    printStr(collect("  ".splitWhitespace()).toStr())
    printStr(collect("a".splitWhitespace()).toStr())
    printStr(collect("a b".splitWhitespace()).toStr())
    printStr(collect("a  b".splitWhitespace()).toStr())
    printStr(collect(" a b".splitWhitespace()).toStr())
    printStr(collect("a b ".splitWhitespace()).toStr())
    printStr(collect("  a  b   ".splitWhitespace()).toStr())

    printStr("---")

    printStr(collect("  ".substr(1, 2).splitWhitespace()).toStr())
    printStr(collect("a".substr(1, 1).splitWhitespace()).toStr())
    printStr(collect("a b".substr(1, 3).splitWhitespace()).toStr())
    printStr(collect("a  b".substr(1, 4).splitWhitespace()).toStr())
    printStr(collect(" a b".splitWhitespace()).toStr())

# expected stdout:
# []
# []
# [a]
# [a,b]
# [a,b]
# [a,b]
# [a,b]
# [a,b]
# ---
# []
# []
# [b]
# [b]
# [a,b]
