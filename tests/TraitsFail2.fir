trait ToStr[a]:
    toStr(self: a): Str

f[ToStr[a]](a: a)
    printStr(a.toStr())

g() = f(123u32)

prim type Str
prim type I32
prim printStr(s: Str): ()

# args: --typecheck --no-prelude --no-backtrace
# expected stderr: tests/TraitFail2.fir:12:7: Type U32 does not implement trait ToStr
