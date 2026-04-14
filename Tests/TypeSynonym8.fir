trait Foo[t]:
    type Item
    foo(self: t, item: Foo[t].Item)

impl Foo[U32]:
    type Item = U64
    foo(self: U32, item: Item): ()

# args: --typecheck
