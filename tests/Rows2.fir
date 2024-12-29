fn mono_fn(alts: [A(I32), B(Str)]) =
    match alts:
        `A(i): printStr("A(i=`i.toStr()`)")
        `B(s): printStr("B(s=`s`)")

fn poly_fn[R](alts: [A(I32), B(Str), ..R]) =
    match alts:
        `A(i): printStr("A(i=`i.toStr()`)")
        `B(s): printStr("B(s=`s`)")
        _: printStr("Other")

fn main() =
    mono_fn(`A(123))
    mono_fn(`B("hi"))
    poly_fn(`A(123))
    poly_fn(`C(Bool.False))
