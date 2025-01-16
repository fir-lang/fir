prim type I32

trait T[a]:
    a(self)
    b(self)

impl T[I32]:
    a(self) = ()

# args: --typecheck --no-prelude --no-backtrace
# expected stderr: tests/TraitImplFail3.fir:7:1: Trait methods missing: ["b"]
