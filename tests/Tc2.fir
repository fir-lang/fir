prim type I32

trait T[a]:
    getI32(self: a): I32

type A:
    i: I32

A.getI32(self: A): I32
    self.i

# args: --typecheck --no-prelude
