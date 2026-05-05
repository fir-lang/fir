#[NoImplicitPrelude]
import []


type A


type Foo(
    x: A,
    x: A,
)

# args: --typecheck
# expected exit status: 101
# expected stderr: Tests/DuplicateFieldFail.fir:10:8: Field x defined multiple times
