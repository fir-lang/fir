type A:
    x: I32

type B:
    y: Str

type C:
    t: Bool

mono_fn(alts: [A, B]):
    match alts:
        ~A(x = i): printStr("A(i=`i.toStr()`)")
        ~B(y = s): printStr("B(s=`s`)")

poly_fn[VarRow[r]](alts: [A, B, ..r]):
    match alts:
        ~A(x = i): printStr("A(i=`i.toStr()`)")
        ~B(y = s): printStr("B(s=`s`)")
        _: printStr("Other")

if_variants_mono() [A, B]:
    if Bool.True:
        ~A(x = 123)
    else:
        ~B(y = "ahoy")

if_variants_poly[VarRow[r]]() [A, B, ..r]:
    if Bool.True:
        ~A(x = 123)
    else:
        ~B(y = "ahoy")

poly_return[VarRow[r]]() [B, ..r]:
    ~B(y = "ahoy")

main():
    mono_fn(~A(x = 123))
    mono_fn(~B(y = "hi"))

    # [A(I32), ..r1] ~ [A(I32), B(Str), ..r2]
    # r1 --> [B(Str), ..r3]
    # r2 --> [..r3]
    # During monomorphisation, r3 should be defaulted as [].
    poly_fn(~A(x = 123))

    # [C(Bool), ..r1] ~ [A(I32), B(Str), ..r2]
    # r1 --> [A(I32), B(Str), ..r3]
    # r2 --> [C(Bool), ..r3]
    # Similar to the previous, r3 should be defaulted as [].
    poly_fn(~C(t = Bool.False))

    if_variants_mono()
    if_variants_poly()
    poly_fn(poly_return())
    ()

# expected stdout:
# A(i=123)
# B(s=hi)
# A(i=123)
# Other
# B(s=ahoy)
