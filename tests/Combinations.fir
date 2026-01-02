combinations(elems: Vec[U32], picksLeft: U32) Vec[Vec[U32]]:
    if picksLeft == 0:
        return Vec.[Vec.[]]

    if picksLeft == elems.len():
        return Vec.[elems]

    if picksLeft > elems.len():
        return Vec.[]

    let rest: Vec[U32] = Vec.fromIter(elems.iter().skip(1))
    let elem = elems.get(0)

    # Combinations with the current element picked.
    let picks1 = combinations(rest, picksLeft - 1)
    for pick: Vec[U32] in picks1.iter():
        pick.insert(0, elem)

    # Combinations with the current element not picked.
    let picks2 = combinations(rest, picksLeft)

    Vec.fromIter(picks1.iter().chain(picks2.iter()))


test(elems: Vec[U32], pick: U32):
    print("(`elems.len()`, `pick`) = `combinations(elems, pick)`")


main():
    test(Vec.[], 0)
    test(Vec.[], 1)
    test(Vec.[u32(1)], 0)
    test(Vec.[u32(1)], 1)
    test(Vec.[u32(1)], 2)

    test(Vec.[u32(1), u32(2), u32(3)], 0)
    test(Vec.[u32(1), u32(2), u32(3)], 1)
    test(Vec.[u32(1), u32(2), u32(3)], 2)
    test(Vec.[u32(1), u32(2), u32(3)], 3)

# expected stdout:
# (0, 0) = [[]]
# (0, 1) = []
# (1, 0) = [[]]
# (1, 1) = [[1]]
# (1, 2) = []
# (3, 0) = [[]]
# (3, 1) = [[1],[2],[3]]
# (3, 2) = [[1,2],[1,3],[2,3]]
# (3, 3) = [[1,2,3]]
