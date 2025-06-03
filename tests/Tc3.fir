prim type I32

trait T[a]:
    test(self: a) ()

    getI32(self: a) I32:
        0

type A:
    i: I32

impl T[A]:
    test(self: A) ():
        self.getI32()
        ()

# args: --typecheck --no-prelude
