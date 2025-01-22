prim type Str
prim type I32

prim printStr(s: Str): ()

trait ToStr[a]:
    toStr(self): Str

type A

A.f[a: ToStr](self, a: a)
    printStr(a.toStr())

# args: --typecheck --no-prelude
