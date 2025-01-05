prim type Str

prim type U32

trait ToStr[t]:
    fn toStr(self): Str

impl ToStr for U32:
    prim fn toStr(self): Str

trait GetItem[x]:
    type Item
    fn getItem(self): Item

type Box[t]:
    thing: t

impl[t] GetItem for Box[t]:
    type Item = t
    fn getItem(self): t = self.thing

fn getItem[a, x: GetItem[Item = a]](x: x): a = x.getItem()

prim fn printStr(s: Str)

fn main() =
    let box = Box(thing = 123u32)
    let item = getItem(box)
    printStr(item.toStr())

# args: --typecheck --no-prelude
