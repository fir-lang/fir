import [Fir/C as C]


main() / exn:
    let x: U32 = C/inline[U32, asdf]("123")

# args: --typecheck
# expected exit status: 101
# expected stderr: Tests/C/InlineTypeParamChecking2.fir:5:32: Unknown type variable asdf
