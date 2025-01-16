prim type I32

type A:
    i: I32

type B:
    i: I32

trait Test[a]:
    type T
    test(self): T

impl Test for A:
    type T = I32
    test(self): T
        123

impl Test for B:
    type T = I32
    test(self): I32
        123

# args: --typecheck --no-prelude
