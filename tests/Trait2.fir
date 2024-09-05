prim type Str
prim type I32

prim fn printStr(s: Str): ()

trait ToStr[A]:
    fn toStr(self): Str

type A

impl A:
    fn f[A: ToStr](self, a: A) =
        printStr(a.toStr())

# args: --typecheck --no-prelude
