permutations(elems: Vec[U32]) Vec[Vec[U32]]:
    if elems.isEmpty():
        return Vec.[Vec.[]]

    let ret: Vec[Vec[U32]] = Vec.empty()

    for elemIdx: U32 in range(u32(0), elems.len()):
        let elem = elems.get(elemIdx)
        let rest = elems.clone()
        rest.remove(elemIdx)
        for p: Vec[U32] in permutations(rest).iter():
            p.insert(0, elem)
            ret.push(p)

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
