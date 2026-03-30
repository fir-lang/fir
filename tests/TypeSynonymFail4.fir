type Foo = U32

main():
    let x: Foo[U32] = 1

# expected exit status: 101
# expected stderr: tests/TypeSynonymFail4.fir:4:12: Incorrect number of type arguments to Foo, expected 0, found 1
