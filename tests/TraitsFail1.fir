#[NoImplicitPrelude]
import []

prim type Str
prim type I32

prim printStr(s: Str) ()

trait ToStr[a]:
    toStr(self: a) Str

f(a: a):
    printStr(a.toStr())

# args: --typecheck
# expected exit status: 101
# expected stderr:
# Unable to resolve predicates:
# tests/TraitsFail1.fir:13:14: ToStr[a]
