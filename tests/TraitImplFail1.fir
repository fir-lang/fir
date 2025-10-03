prim type I32

trait T[a]:
    a(self: a)
    b(self: a)

impl T[I32]:
    a(self: I32): ()

# args: --typecheck --no-prelude
# expected stderr: tests/TraitImplFail1.fir:7:1: Trait methods missing: ["b"]
