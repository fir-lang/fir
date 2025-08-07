type A(x: I32)

type B(y: Str)

type C:
    C

mono_fn(alts: [A, B]):
    match alts:
        ~A(x = i): printStr("A(i=`i.toStr()`)")
        ~B(y = s): printStr("B(s=`s`)")

main(): mono_fn(~C.C)

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/RowsFail4.fir:13:17: Unable to unify variant with constructors {"C"} with variant with constructors {"A", "B"}
