type T:
    i: I32

impl I32[T]:
    test(self: T) = ()

prim type I32

# args: --no-prelude --typecheck --no-backtrace
# expected stderr: tests/TraitFail3.fir:4:1: I32 in impl declararation is not a trait
