#[NoImplicitPrelude]
import []

trait Foo[t]:
    type A
    type A

# args: --typecheck
# expected exit status: 101
# expected stderr: Tests/AssocTysFail1.fir:6:10: Associated type A declared multiple times
