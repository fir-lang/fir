#[NoImplicitPrelude]
import []

trait Test[t1, t2]:
    test(self: t1) t2

type Type1

impl Test[Type1, Type1]:
    test(self: Type1) Type1:
        self

main():
    let t1 = Type1
    let x: Type1 = t1.test()

# args: --typecheck
