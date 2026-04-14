#[NoImplicitPrelude]
import [
    Tests/Modules/ImportMatching/Lib as L,
    Tests/Modules/ImportMatching/Lib/[fun1],
]


main():
    fun1(L/Type1.Con1)
    L/fun1(L/Type1.Con2)


# args: --typecheck
