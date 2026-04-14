#[NoImplicitPrelude]
import []

type Type1

type Type2

trait ToStr[a]:
    toStr(self: a) Type1

f[ToStr[a]](a: a):
    printStr(a.toStr())

g(): f(Type2)

prim printStr(s: Type1) ()

# args: --typecheck
# expected exit status: 101
# expected stderr:
# Unable to resolve predicates:
# Tests/TraitsFail2.fir:14:6: ToStr[Type2]
