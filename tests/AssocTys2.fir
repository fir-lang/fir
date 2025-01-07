prim type I32

prim type Str

impl I32:
    prim fn toStr(self): Str

trait Test[t]:
    type Elem

    fn getElem(self): Elem

impl Test for I32:
    type Elem = Str

    fn getElem(self): Str = self.toStr()

fn expectStrElem[x: Test[Elem = Str]](x: x): Str = x.getElem()

fn main()
    expectStrElem(123i32)
    ()

# args: --typecheck --no-prelude
