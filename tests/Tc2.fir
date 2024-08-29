prim type I32

trait T[A]:
    fn getI32(self): I32

type A:
    i: I32

impl T[A]:
    fn getI32(self): I32 =
        self.i

# args: --typecheck --no-prelude
