prim type Str
prim type I32

prim printStr(s: Str) ()

trait ToStr[a]:
    toStr(self: a) Str

f(a: a):
    printStr(a.toStr())

# args: --typecheck --no-prelude --no-backtrace
# expected exit status: 101
# expected stderr: tests/TraitsFail1.fir:10:14: Unable to resolve pred ToStr[a]
