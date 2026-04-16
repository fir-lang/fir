# Defined names should shadow imported ones.

import [
    Tests/Modules/ImportOverride1/Lib,
    Tests/Modules/ImportOverride1/Lib as Lib,
    Tests/Modules/ImportOverride1/Lib/[Foo as Foo2],
]


type Foo(
    x: U32,
    y: U32,
)


test(foo: Foo):
    print("Main/Foo(x = `foo.x`, y = `foo.y`)")


main():
    test(Foo(x = 1, y = 2))
    Lib/test(Foo2(a = "hi", b = "bye"))


# expected stdout:
# Main/Foo(x = 1, y = 2)
# Lib/Foo(a = hi, b = bye)
