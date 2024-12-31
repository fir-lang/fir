fn mono_fn(alts: [A(x: I32), B(y: Str)]) =
    match alts:
        `A(x = i): printStr("A(i=`i.toStr()`)")
        `B(y = s): printStr("B(s=`s`)")

fn main() = mono_fn(`C())

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/RowsFail4.fir:6:21: Unable to unify variant with constructors {"C"} with variant with constructors {"A", "B"}

