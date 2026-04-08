#[NoImplicitPrelude]
import []

type T(i: I32)

impl I32[T]:
    test(self: T): ()

prim type I32

# args: --typecheck
# expected exit status: 101
# expected stderr: tests/TraitsFail3.fir:6:1: I32 in impl declararation is not a trait
