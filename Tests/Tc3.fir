#[NoImplicitPrelude]
import []

type Type1

trait T[a]:
    test(self: a) ()

    getI32(self: a) Type1:
        Type1

type A(i: Type1)

impl T[A]:
    test(self: A) ():
        self.getI32()
        ()

# args: --typecheck
