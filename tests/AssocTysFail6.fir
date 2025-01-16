prim type I32

prim type Str

impl I32:
    prim toStr(self): Str

trait Test[t]:
    type Elem

    getElem(self): Elem

impl Test for I32:
    type Elem = Str

    getElem(self): Str = self.toStr()

expectI32Elem[x: Test[Elem = I32]](x: x): I32 = x.getElem()

main()
    expectI32Elem(123i32)
    ()

# args: --typecheck --no-prelude --no-backtrace
# expected stderr: tests/AssocTysFail6.fir:21:5: Unable to unify types Str and I32
