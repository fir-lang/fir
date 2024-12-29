fn exhaustive[R](alts: [A(I32), B(Str), ..R]) =
    match alts:
        `A(i): printStr("A(i=`i.toStr()`)")
        `B(s): printStr("B(s=`s`)")

fn main() =
    exhaustive(`A(123))
    exhaustive(`B("hi"))
