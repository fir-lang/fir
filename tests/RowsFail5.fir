fn poly_fn[R](alts: [A(x: I32), B(y: Str), ..R]) =
    match alts:
        `A(x = i): printStr("A(i=`i.toStr()`)")
        `B(y = s): printStr("B(s=`s`)")
        _: printStr("Other")

fn main() = poly_fn(`B(y = Bool.False))

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr: tests/RowsFail5.fir:7:21: Unable to unify types Bool and Str
