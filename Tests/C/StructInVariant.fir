#[include("stdlib.h")]
import [Fir/C as C]


extern type DivT = "div_t"(
    quot: I32 = "quot",
    rem: I32 = "rem",
)


pickOne(b: Bool) [DivT, Bool]:
    if b:
        ~DivT(quot = 12, rem = 34)
    else:
        ~Bool.False


showVariant(v: [DivT, Bool]):
    match v:
        ~DivT(quot, rem):
            printStr("DivT: quot = `quot`, rem = `rem`")
        ~Bool.True:
            printStr("Bool.True")
        ~Bool.False:
            printStr("Bool.False")


main():
    showVariant(pickOne(Bool.True))
    showVariant(pickOne(Bool.False))


# expected stdout:
# DivT: quot = 12, rem = 34
# Bool.False
