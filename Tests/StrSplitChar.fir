main():
    print(collectCheckLen("".splitChar('a'), 1))
    print(collectCheckLen("bbb".splitChar('a'), 1))
    print(collectCheckLen("aa".splitChar('a'), 3))
    print(collectCheckLen("a a a".splitChar(' '), 3))
    print(collectCheckLen(" a ".splitChar(' '), 3))
    print(collectCheckLen("baab".splitChar('b'), 3))
    print(collectCheckLen("abba".splitChar('b'), 3))


collectCheckLen(iter: SplitChar, expectedLen: U32) Vec[Str]:
    let vec = Vec.fromIter(iter)
    if vec.len() != expectedLen:
        panic("Vec = `vec`, expected len = `expectedLen`, actual len = `vec.len()`")
    vec

# expected stdout:
# []
# [bbb]
# [,,]
# [a,a,a]
# [,a,]
# [,aa,]
# [a,,a]
