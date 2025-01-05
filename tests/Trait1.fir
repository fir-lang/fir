prim type Str
prim type I32

prim fn printStr(s: Str): ()

trait ToStr[a]:
    fn toStr(self): Str

fn f[a: ToStr](a: a) =
    printStr(a.toStr())

# args: --typecheck --no-prelude
