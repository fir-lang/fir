prim type Str
prim type I32

prim printStr(s: Str): ()

trait ToStr[a]:
    toStr(self): Str

f[a: ToStr](a: a)
    printStr(a.toStr())

g() = f(123u32)

# args: --typecheck --no-prelude --no-backtrace
# expected stderr: tests/TraitFail2.fir:12:7: Type U32 does not implement trait ToStr
