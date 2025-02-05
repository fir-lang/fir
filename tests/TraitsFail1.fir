prim type Str
prim type I32

prim printStr(s: Str): ()

trait ToStr[a]:
    toStr(self: a): Str

f(a: a)
    printStr(a.toStr())

# args: --typecheck --no-prelude --no-backtrace
# expected exit status: 101
# expected stderr: tests/TraitFail1.fir:10:14: Type a does not have field or method toStr
