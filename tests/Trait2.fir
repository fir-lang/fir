prim type Str
prim type I32

prim fn printStr(s: Str): ()

trait ToStr[a]:
    fn toStr(self): Str

type A

impl A:
    fn f[a: ToStr](self, a: a) =
        printStr(a.toStr())

# args: --typecheck --no-prelude
