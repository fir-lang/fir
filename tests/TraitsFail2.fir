trait ToStr[a]:
    toStr(self: a): Str

f[ToStr[a]](a: a)
    printStr(a.toStr())

g() = f(123u32)

prim type Str
prim type I32
prim printStr(s: Str): ()

# args: --typecheck --no-prelude --no-backtrace
# expected exit status: 101
# expected stderr: tests/TraitsFail2.fir:7:7: Unable to resolve pred ToStr[U32]
