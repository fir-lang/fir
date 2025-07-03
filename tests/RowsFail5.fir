type A:
    x: I32

type B:
    y: Str

poly_fn(alts: [A, B, ..r]):
    match alts:
        ~A(x = i): printStr("A(i=`i.toStr()`)")
        ~B(y = s): printStr("B(s=`s`)")
        _: printStr("Other")

main(): poly_fn(~B(y = Bool.False))

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr: tests/RowsFail5.fir:13:24: Unable to unify types Bool and Str
