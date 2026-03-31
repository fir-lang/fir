type Item[exts]:
    A(
        x: U32,
        ..ItemExts[exts].A
    )
    B(
        msg: Str,
        ..ItemExts[exts].B
    )


trait ItemExts[t]:
    type A: Row[Rec]

    type B: Row[Rec]

    defaultA() (..A)

    defaultB() (..B)


type Defaults1


impl ItemExts[Defaults1]:
    type A = row(def1Ext1: U32)

    type B = row(def1Ext2: Bool)

    defaultA() (..A):
        (def1Ext1 = u32(1))

    defaultB() (..B):
        (def1Ext2 = Bool.True)


type Defaults2


impl ItemExts[Defaults2]:
    type A = row(def2Ext1: Str)

    type B = row(def2Ext2: Option[U32])

    defaultA() (..A):
        (def2Ext1 = "hi")

    defaultB() (..B):
        (def2Ext2 = Option.Some(u32(1)))


impl[ToStr[RecRowList[ItemExts[exts].A]], ToStr[RecRowList[ItemExts[exts].B]],] ToStr[Item[exts]]:
    toStr(self: Item[exts]) Str:
        match self:
            Item.A(x, ..rest): "A(x = `x`, rest = `rest`)"
            Item.B(msg, ..rest): "B(msg = `msg`, rest = `rest`)"
