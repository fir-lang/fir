# Regression test: a local type synonym that shares a simple name with a type
# imported via a module prefix, with different arities.

import [Tests/Modules/SynonymPrefixConflict/Lib as Lib]


type Foo = Lib/Foo[U32]


main():
    let foo: Foo = Lib/mkFoo(u32(42))
    print(foo.item)


# expected stdout: 42
