prim type Str
prim type I32

prim fn printStr(s: Str): ()

trait ToStr[A]:
    fn toStr(self): Str

fn f[A: ToStr](a: A) =
    printStr(a.toStr())

# args: --typecheck --no-prelude
