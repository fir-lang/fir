prim type I32

trait T[a]:
    a(self)

impl T for I32:
    a(self) = ()
    b(self) = ()

# args: --typecheck --no-prelude --no-backtrace
# expected stderr: tests/TraitImplFail2.fir:8:5: Trait T does not have a method named b
