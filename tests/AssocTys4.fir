prim printStr(s: Str)

prim type Str

prim type U32

trait ToStr[t]:
    toStr(self): Str

impl ToStr for U32:
    prim toStr(self): Str

trait GetItem[x]:
    type Item
    getItem(self): Item

type Box[t]:
    thing: t

impl[t] GetItem for Box[t]:
    type Item = t
    getItem(self): t = self.thing

getItem[a, x: GetItem[Item = a]](x: x): a = x.getItem()

main()
    let box = Box(thing = 123u32)
    let item = getItem(box)

# args: --typecheck --no-prelude
