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

fn expectI32Elem[X: Test[Elem = I32]](x: X): I32 = x.getElem()

fn main() =
    expectI32Elem(123i32)
    ()

# args: --typecheck --no-prelude --no-backtrace
# expected stderr: tests/AssocTysFail6.fir:21:5: Unable to unify types Str and I32
