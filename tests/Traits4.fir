trait ToStr[a]:
    toStr(self: a): Str

type A

A.f[ToStr[a]](self, a: a)
    printStr(a.toStr())

prim type Str
prim type I32
prim printStr(s: Str): ()

# args: --typecheck --no-prelude
