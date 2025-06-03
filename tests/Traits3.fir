trait ToStr[a]:
    toStr(self: a) Str

f[ToStr[a]](a: a):
    printStr(a.toStr())

prim type Str
prim type I32
prim printStr(s: Str) ()

# args: --typecheck --no-prelude
