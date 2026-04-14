#[NoImplicitPrelude]
import []

trait Foo[t]:
    type A

    getA() Foo[t].A

type Type1

type Type2

impl Foo[Type1]:
    type A = Type2

    getA() Foo[Type1].A:
        Type2

main():
    let x: Type1 = Foo.getA[Type1, []]()
    ()

# args: --typecheck
# expected exit status: 101
# expected stderr: Tests/AssocTysFail5.fir:20:20: Unable to unify types Type2 and Type1
