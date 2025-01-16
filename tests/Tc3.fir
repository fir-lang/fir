prim type I32

trait T[a]:
    test(self): ()

    getI32(self): I32
        0

type A:
    i: I32

impl T for A:
    test(self): ()
        self.getI32()
        ()

# args: --typecheck --no-prelude
