type CombinationsIter(
    elems: Vec[U32],
    pick: U32,
    work: Vec[CombinationWork],
)


type CombinationWork(
    combination: Vec[U32],
    suffixStart: U32,
)


combinations(elems: Vec[U32], n: U32) CombinationsIter:
    CombinationsIter(
        elems,
        pick = n,
        work = Vec.[CombinationWork(combination = Vec.[], suffixStart = 0)],
    )


impl Iterator[CombinationsIter, Vec[U32], exn]:
    next(self: CombinationsIter) Option[Vec[U32]] / exn:
        while self.work.pop() is Option.Some(work):
            if work.combination.len() == self.pick:
                return Option.Some(work.combination)

            if self.pick - work.combination.len()
                    == self.elems.len() - work.suffixStart:
                work.combination.extend(self.elems.iter().skip(work.suffixStart))
                return Option.Some(work.combination)

            if work.suffixStart == self.elems.len():
                continue

            self.work.push(
                CombinationWork(
                    combination = work.combination,
                    suffixStart = work.suffixStart + 1,
                ),
            )

            let newCombination = work.combination.clone()
            newCombination.push(self.elems.get(work.suffixStart))
            self.work.push(
                CombinationWork(
                    combination = newCombination,
                    suffixStart = work.suffixStart + 1,
                ),
            )

        Option.None


test(elems: Vec[U32], pick: U32):
    let cs: Vec[Vec[U32]] = Vec.fromIter(combinations(elems, pick))
    print("(`elems.len()`, `pick`) = `cs`")


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
