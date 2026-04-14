#[NoImplicitPrelude]
import []

type Type1

type Type2

type Type3

trait Foo[t]:
    type Item = Type1
    type MyRow: Row[Rec] = row()
    getItem(self: t) Item
    getRecord(self: t) (..MyRow)

impl Foo[Type1]:
    getItem(self: Type1) Item:
        self

    getRecord(self: Type1) (..MyRow):
        ()

impl Foo[Type2]:
    type Item = Type2

    type MyRow = row(msg: Type3)

    getItem(self: Type2) Item:
        self

    getRecord(self: Type2) (..MyRow):
        (msg = Type3)

# args: --typecheck
