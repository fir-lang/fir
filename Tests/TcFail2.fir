#[NoImplicitPrelude]
import []

prim type Str
prim type I32

type Bool:
    False
    True

Bool.toStr(self) Str:
    Bool.False

# args: --typecheck
# expected exit status: 101
# expected stderr: Tests/TcFail2.fir:12:5: Unable to unify types Bool and Str
