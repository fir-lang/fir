prim type I32

trait T[A]:
    fn a(self)
    fn b(self)

impl T[I32]:
    fn a(self) = ()

# args: --typecheck --no-prelude --no-backtrace
# expected stderr: tests/TraitImplFail1.fir:7:1: Trait methods missing: ["b"]
