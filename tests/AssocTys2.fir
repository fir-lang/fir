prim type I32

prim type Str

impl I32:
    prim fn toStr(self): Str

trait Test[T]:
    type Elem

    fn getElem(self): Elem

impl Test for I32:
    type Elem = Str

    fn getElem(self): Str = self.toStr()

fn expectStrElem[X: Test[Elem = Str]](x: X): Str = x.getElem()

fn main() =
    expectStrElem(123i32)
    ()

# args: --typecheck --no-prelude
