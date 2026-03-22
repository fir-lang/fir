trait Foo[t]:
    type Item
    getItem(self: t) Foo[t].Item

type MyType:
    MyType

impl Foo[MyType]:
    type Item = I32
    getItem(self: MyType) I32:
        42

# args: --typecheck
