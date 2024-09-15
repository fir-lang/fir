prim type I32

trait T[A]:
    fn a(self)

impl T[I32]:
    fn a(self) = ()
    fn b(self) = ()

# args: --typecheck --no-prelude --no-backtrace
# expected stderr: tests/TraitImplFail2.fir:8:5: Trait T does not have a method named b
