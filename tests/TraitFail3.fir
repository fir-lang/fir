type T:
    i: I32

impl I32 for T:
    test(self) = ()

# args: --typecheck --no-backtrace
# expected stderr: tests/TraitFail3.fir:4:1: I32 in impl declararation is not a trait
