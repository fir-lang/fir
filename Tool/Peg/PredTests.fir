import [
    Compiler/Error,
    Compiler/Lexer,
    Tool/Peg/PegTestLib,
    Tool/Peg/TestGrammarPreds,
]


main():
    let items1: Vec[Item[Defaults1]] = try(
        \(): runParser("a b", items, Bool.False),
    ).unwrap()

    print(items1)

    let items2: Vec[Item[Defaults2]] = try(
        \(): runParser("a b", items, Bool.False),
    ).unwrap()

    print(items2)


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


# expected stdout:
# [A(x = 0, rest = (def1Ext1 = 1)),B(msg = hi, rest = (def1Ext2 = Bool.True))]
# [A(x = 0, rest = (def2Ext1 = hi)),B(msg = hi, rest = (def2Ext2 = Option.Some(1)))]
