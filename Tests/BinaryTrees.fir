# This is the ["binary-trees"][1] benchmark from ["The Computer Language
# Benchmarks Game"][2].
#
# I'm not sure how useful this benchmark is, but it should serve as a test + a
# port of a program that many people are already familiar with.
#
# [1]: https://benchmarksgame-team.pages.debian.net/benchmarksgame/index.html
# [2]: https://benchmarksgame-team.pages.debian.net/benchmarksgame/performance/binarytrees.html


main():
    let n = match getArgs().getOpt(1):
        Option.Some(nStr): parseU32(nStr).unwrap()
        Option.None: 10

    let minDepth = u32(4)
    let maxDepth = max(minDepth + u32(2), n)

    do:
        let stretchTree = genTree(maxDepth + 1)
        let stretchTreeSize = itemCheck(stretchTree)
        print("stretch tree of depth `maxDepth + 1`\t check: `stretchTreeSize`")

    let longLivedTree = genTree(maxDepth)

    let msgs: Vec[Str] = Vec.empty()

    for n in irange(minDepth / 2, maxDepth / 2):
        let depth = n * u32(2)
        let iter = u32(1) << (maxDepth - depth + minDepth)
        msgs.push(bench(depth, iter))

    for msg in msgs.iter():
        print(msg)

    print(
        "long lived tree of depth `maxDepth`\t check: `itemCheck(longLivedTree)`",
    )


type Tree(
    left: Option[Tree],
    right: Option[Tree],
)


itemCheck(tree: Tree) U32:
    if tree is Tree(left = Option.Some(left), right = Option.Some(right)):
        u32(1) + itemCheck(left) + itemCheck(right)
    else:
        u32(1)


genTree(depth: U32) Tree:
    let tree = Tree(left = Option.None, right = Option.None)
    if depth != 0:
        tree.left = Option.Some(genTree(depth - 1))
        tree.right = Option.Some(genTree(depth - 1))
    tree


bench(depth: U32, iter: U32) Str:
    let sum = u32(0)
    for _ in range(u32(0), iter):
        sum += itemCheck(genTree(depth))
    "`iter`\t trees of depth `depth`\t check: `sum`"


# ------------------------------------------------------------------------------
# Things that should be in the standard library.


type ParseIntError:
    EmptyInput
    InvalidDigit
    Overflow


impl ToStr[ParseIntError]:
    toStr(self: ParseIntError) Str:
        match self:
            ParseIntError.EmptyInput: "empty input"
            ParseIntError.InvalidDigit: "invalid digit"
            ParseIntError.Overflow: "overflow"


parseU32(s: Str) Result[ParseIntError, U32]:
    if s.len() == 0:
        return Result.Err(ParseIntError.EmptyInput)

    let result: U32 = 0

    for c in s.chars():
        if c < '0' or c > '9':
            return Result.Err(ParseIntError.InvalidDigit)

        let digit = c.asU32() - '0'.asU32()

        result = match checkedMul(result, 10):
            Option.None: return Result.Err(ParseIntError.Overflow)
            Option.Some(newResult): newResult

        result = match checkedAdd(result, digit):
            Option.None: return Result.Err(ParseIntError.Overflow)
            Option.Some(newResult): newResult

    Result.Ok(result)


checkedAdd(i1: U32, i2: U32) Option[U32]:
    if i1 > u32(4294967295) - i2:
        return Option.None

    Option.Some(i1 + i2)


checkedMul(i1: U32, i2: U32) Option[U32]:
    let result = i1 * i2

    if i1 != 0 and result / i1 != i2:
        return Option.None

    Option.Some(result)


# ------------------------------------------------------------------------------


# expected stdout:
# stretch tree of depth 11	 check: 4095
# 1024	 trees of depth 4	 check: 31744
# 256	 trees of depth 6	 check: 32512
# 64	 trees of depth 8	 check: 32704
# 16	 trees of depth 10	 check: 32752
# long lived tree of depth 10	 check: 2047
