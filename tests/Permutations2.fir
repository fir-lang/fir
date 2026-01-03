permutations(elems: Vec[U32]) Vec[Vec[U32]]:
    let work: Vec[(p: Vec[U32], elems: Vec[U32])] = Vec.[
        (p = Vec.[], elems = elems),
    ]

    let ret: Vec[Vec[U32]] = Vec.[]

    while work.pop() is Option.Some((p, elems)):
        if elems.isEmpty():
            ret.push(p)

        for elemIdx: U32 in range(u32(0), elems.len()):
            let remainingElems: Vec[U32] = Vec.fromIter(elems.iter())
            remainingElems.remove(elemIdx)
            let pNext = p.clone()
            pNext.push(elems.get(elemIdx))
            work.push((p = pNext, elems = remainingElems))

    ret.reverse()
    ret


test(elems: Vec[U32]):
    print("`elems.len()` = `permutations(elems)`")


main():
    test(Vec.[])
    test(Vec.[u32(1)])
    test(Vec.[u32(1), u32(2)])
    test(Vec.[u32(1), u32(2), u32(3)])


# expected stdout:
# 0 = [[]]
# 1 = [[1]]
# 2 = [[1,2],[2,1]]
# 3 = [[1,2,3],[1,3,2],[2,1,3],[2,3,1],[3,1,2],[3,2,1]]
