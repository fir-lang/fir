fn mono_fn(alts: [A(x: I32), B(y: Str)]) =
    match alts:
        `A(x = i): printStr("A(i=`i.toStr()`)")
        `B(y = s): printStr("B(s=`s`)")

fn poly_fn[R](alts: [A(x: I32), B(y: Str), ..R]) =
    match alts:
        `A(x = i): printStr("A(i=`i.toStr()`)")
        `B(y = s): printStr("B(s=`s`)")
        _: printStr("Other")

fn main() =
    mono_fn(`A(x = 123))
    mono_fn(`B(y = "hi"))

    # [A(I32), ..R1] ~ [A(I32), B(Str), ..R2]
    # R1 --> [B(Str), ..R3]
    # R2 --> [..R3]
    # During monomorphisation, R3 should be defaulted as [].
    poly_fn(`A(x = 123))

    # [C(Bool), ..R1] ~ [A(I32), B(Str), ..R2]
    # R1 --> [A(I32), B(Str), ..R3]
    # R2 --> [C(Bool), ..R3]
    # Similar to the previous, R3 should be defaulted as [].
    poly_fn(`C(t = Bool.False))
