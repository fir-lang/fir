main():
    print(range(u32(0), u32(10)).size[RangeIterator[U32], U32, [], []]())
    print(
        range(u32(0), u32(10)).take(0)
            .size[Take[RangeIterator[U32], U32, []], U32, [], []](),
    )
    print(
        range(u32(0), u32(10)).take(5)
            .size[Take[RangeIterator[U32], U32, []], U32, [], []](),
    )
    print(
        range(u32(0), u32(10)).take(10)
            .size[Take[RangeIterator[U32], U32, []], U32, [], []](),
    )
    print(
        range(u32(0), u32(10)).take(11)
            .size[Take[RangeIterator[U32], U32, []], U32, [], []](),
    )


# expected stdout:
# Option.Some(10)
# Option.Some(0)
# Option.Some(5)
# Option.Some(10)
# Option.Some(10)
