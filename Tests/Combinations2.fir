combinations(elems: Vec[U32], n: U32) Vec[Vec[U32]]:
    if n == 0:
        return Vec.[Vec.[]]

    if n > elems.len():
        return Vec.[]

    if n == elems.len():
        return Vec.[elems.clone()]

    # n < elems.len()
    let work: Vec[(c: Vec[U32], suffixStart: U32)] = Vec.[
        (c = Vec.[], suffixStart = u32(0)),
    ]

    let ret: Vec[Vec[U32]] = Vec.[]

    while work.pop() is Option.Some((c, suffixStart)):
        if c.len() == n:
            ret.push(c)
            continue

        if n - c.len() == elems.len() - suffixStart:
            c.extend(elems.iter().skip(suffixStart))
            ret.push(c)
            continue

        work.push((c = c, suffixStart = suffixStart + 1))

        let c1 = c.clone()
        c1.push(elems.get(suffixStart))
        work.push((c = c1, suffixStart = suffixStart + 1))

    ret


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
