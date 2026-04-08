#[NoImplicitPrelude]
import []

prim type U32
prim type U64
prim type Str

trait Foo[t]:
    type Item = U32
    type MyRow: Row[Rec] = row()
    getItem(self: t) Item
    getRecord(self: t) (..MyRow)

impl Foo[U32]:
    getItem(self: U32) Item:
        self

    getRecord(self: U32) (..MyRow):
        ()

impl Foo[U64]:
    type Item = U64

    type MyRow = row(msg: Str)

    getItem(self: U64) Item:
        self

    getRecord(self: U64) (..MyRow):
        (msg = "hi")

# args: --typecheck
