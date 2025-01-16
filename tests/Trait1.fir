prim type Str
prim type I32

prim printStr(s: Str): ()

trait ToStr[a]:
    toStr(self): Str

f[a: ToStr](a: a)
    printStr(a.toStr())

# args: --typecheck --no-prelude
