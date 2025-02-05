prim type I32

trait T[a]:
    a(self: a)

impl T[I32]:
    a(self: a) = ()
    b(self: a) = ()

# args: --typecheck --no-prelude --no-backtrace
# expected exit status: 101
# expected stderr: tests/TraitImplFail2.fir:8:5: Trait T does not have method b
