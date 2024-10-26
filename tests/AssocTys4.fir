prim fn printStr(s: Str)

prim type Str

prim type U32

trait ToStr[T]:
    fn toStr(self): Str

impl ToStr for U32:
    prim fn toStr(self): Str

trait GetItem[X]:
    type Item
    fn getItem(self): Item

type Box[T]:
    thing: T

impl[T] GetItem for Box[T]:
    type Item = T
    fn getItem(self): T = self.thing

fn getItem[A, X: GetItem[Item = A]](x: X): A = x.getItem()

fn main() =
    let box = Box(thing = 123u32)
    let item = getItem(box)

# args: --typecheck --no-prelude
