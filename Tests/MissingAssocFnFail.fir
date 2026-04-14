#[NoImplicitPrelude]
import []

type MyType

main():
    let x: MyType = MyType.test()

# args: --typecheck
# expected exit status: 101
# expected stderr:
# Tests/MissingAssocFnFail.fir:7:21: Type MyType does not have associated function test
