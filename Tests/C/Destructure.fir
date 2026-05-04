#[include("stdlib.h")]
import [Fir/C as C]


extern type DivT = "div_t"(
    quot: I32 = "quot",
    rem: I32 = "rem",
)


cdiv(num: I32, den: I32) DivT:
    C/inline("div(`num`, `den`)")


main():
    let DivT(quot, rem) = cdiv(17, 5)
    printStr("let:   quot = `quot`, rem = `rem`")

    let DivT(quot = q, rem = r) = cdiv(20, 6)
    printStr("rename: q = `q`, r = `r`")

    match cdiv(100, 7):
        DivT(quot, rem):
            printStr("match:  quot = `quot`, rem = `rem`")

    let constructed = DivT(quot = 42, rem = 13)
    let DivT(quot, rem) = constructed
    printStr("alloc:  quot = `quot`, rem = `rem`")


# expected stdout:
# let:   quot = 3, rem = 2
# rename: q = 3, r = 2
# match:  quot = 14, rem = 2
# alloc:  quot = 42, rem = 13
