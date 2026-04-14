type A(x: I32)

type B(y: Str)

type C:
    C

mono_fn(alts: [A, B]):
    match alts:
        ~A(x = i): printStr("A(i=`i.toStr()`)")
        ~B(y = s): printStr("B(s=`s`)")

main(): mono_fn(~C.C)

# args: --typecheck
# expected exit status: 101
# expected stderr: Tests/RowsFail4.fir:13:17: Unable to unify [C, .._1] with [A, B]
