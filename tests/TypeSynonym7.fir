trait Foo[t]:
    type Item
    foo(self: t, item: Item)

impl Foo[U32]:
    type Item = U64
    foo(self: U32, item: Foo[U32].Item): ()

# args: --typecheck
