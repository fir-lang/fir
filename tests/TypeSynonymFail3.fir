type Foo = Vec

main():
    let x: Foo = Vec.withCapacity(10)

# expected exit status: 101
# expected stderr:
# tests/TypeSynonymFail3.fir:1:12: Incorrect number of type arguments to Vec, expected 1, found 0
