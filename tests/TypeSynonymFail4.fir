type Foo = U32

main():
    let x: Foo[U32] = 1

# expected exit status: 101
# expected stderr: tests/TypeSynonymFail4.fir:4:12: Type synonym Foo does not take type arguments
