prim type I32

type A:
    i: I32

type B:
    i: I32

trait Test[A]:
    type T
    fn test(self): T

impl Test[A]:
    type T = I32
    fn test(self): T =
        123

impl Test[B]:
    type T = I32
    fn test(self): I32 =
        123

# args: --typecheck --no-prelude
