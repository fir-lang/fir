prim type I32

trait T[a]:
    getI32(self): I32

type A:
    i: I32

impl T for A:
    getI32(self): I32
        self.i

# args: --typecheck --no-prelude
