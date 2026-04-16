# Defined names should shadow imported ones.

import [
    Tests/Modules/ImportOverride2/Lib,
    Tests/Modules/ImportOverride2/Lib as Lib,
    Tests/Modules/ImportOverride2/Lib/[Foo as Foo2],
]


type Foo(
    x: U32,
    y: U32,
)


Foo.test(self):
    print("Main/Foo(x = `self.x`, y = `self.y`)")


main():
    Foo(x = 1, y = 2).test()
    Lib/Foo(a = "hi", b = "bye").test()
    Foo2(a = "abc", b = "def").test()


# expected stdout:
# Main/Foo(x = 1, y = 2)
# Lib/Foo(a = hi, b = bye)
# Lib/Foo(a = abc, b = def)
