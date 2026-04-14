#[NoImplicitPrelude]
import []

trait Test[t]:
    test(self: t)

type Type1

impl Test[Type1]:
    test(self: Type1):
        ()

main():
    let t1 = Type1
    t1.test()

# args: --typecheck
