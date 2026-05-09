import [Fir/C as C]


main() / []:
    let x: U32 = C/inline[U64, []]("123")

# args: --typecheck
# expected exit status: 101
# expected stderr: Tests/C/InlineTypeParamChecking1.fir:5:36: Unable to unify types U64 and U32
