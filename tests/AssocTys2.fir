prim type I32

prim type Str

prim I32.toStr(self): Str

trait Test[t]:
    type Elem

    getElem(self): Elem

impl Test for I32:
    type Elem = Str

    getElem(self): Str = self.toStr()

expectStrElem[x: Test[Elem = Str]](x: x): Str = x.getElem()

main()
    expectStrElem(123i32)
    ()

# args: --typecheck --no-prelude
