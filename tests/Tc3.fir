prim type I32

trait T[A]:
    fn test(self): ()

    fn getI32(self): I32 =
        0

type A:
    i: I32

impl T[A]:
    fn test(self): () =
        self.getI32()
        ()

# args: --typecheck --no-prelude
# expected stdout:
