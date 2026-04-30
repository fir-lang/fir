#[include("stdlib.h")]
import [Fir/C as C]


extern type DivT = "div_t"(
    quot: I32 = "quot",
    rem: I32 = "rem",
)


div(num: I32, den: I32) DivT:
    C/inline("div(`num`, `den`)")


main():
    let r = div(17, 5)
    printStr("17/5 quot=`r.quot` rem=`r.rem`")

    r.quot = 99
    printStr("after overwrite quot=`r.quot` rem=`r.rem`")


# expected stdout:
# 17/5 quot=3 rem=2
# after overwrite quot=99 rem=2
