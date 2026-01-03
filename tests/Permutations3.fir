type PermutationsIter(
    elems: Vec[U32],
    work: Vec[PermutationWork],
)


type PermutationWork(
    current: Vec[U32],
    remainingElems: Vec[U32],
)


impl Iterator[PermutationsIter, Vec[U32], exn]:
    next(self: PermutationsIter) Option[Vec[U32]] / exn:
        while self.work.pop() is Option.Some(work):
            if work.remainingElems.isEmpty():
                return Option.Some(work.current)

            let elemIdx = work.remainingElems.len() - 1
            loop:
                let remainingElems: Vec[U32] = Vec.fromIter(
                    work.remainingElems.iter(),
                )
                remainingElems.remove(elemIdx)
                let pNext = work.current.clone()
                pNext.push(work.remainingElems.get(elemIdx))
                self.work.push(
                    PermutationWork(
                        current = pNext,
                        remainingElems = remainingElems,
                    ),
                )
                if elemIdx == 0:
                    break
                elemIdx -= 1

        Option.None


permutations(elems: Vec[U32]) PermutationsIter:
    PermutationsIter(
        elems,
        work = Vec.[PermutationWork(current = Vec.[], remainingElems = elems)],
    )


test(elems: Vec[U32]):
    let ps: Vec[Vec[U32]] = Vec.fromIter(permutations(elems))
    print("`elems.len()` = `ps`")


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
