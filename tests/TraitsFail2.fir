trait ToStr[a]:
    toStr(self: a) Str

f[ToStr[a]](a: a):
    printStr(a.toStr())

g(): f(u32(123))

u32(i: U32) U32: i

prim type Str
prim type I32
prim type U32
prim printStr(s: Str) ()

# args: --typecheck --no-prelude --no-backtrace
# expected exit status: 101
# expected stderr: tests/TraitsFail2.fir:7:6: Unable to resolve pred ToStr[U32]
