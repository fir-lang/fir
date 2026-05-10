import [Fir/C as C]


extern type DivT = "div_t"(
    quot: I32 = "quot",
    rem: I32 = "rem",
)


impl Eq[DivT]:
    __eq(self: DivT, other: DivT) Bool:
        self.quot == other.quot and self.rem == other.rem


impl ToStr[DivT]:
    toStr(self: DivT) Str:
        "DivT(quot=`self.quot`, rem=`self.rem`)"


main():
    let a = DivT(quot = 7, rem = 2)
    let b = DivT(quot = 7, rem = 2)
    let c = DivT(quot = 9, rem = 0)

    printStr(a.toStr())
    printStr("a = `a`, c = `c`")

    if a == b:
        printStr("a == b")
    else:
        panic("a != b")

    if a != c:
        printStr("a != c")
    else:
        panic("a == c")


# expected stdout:
# DivT(quot=7, rem=2)
# a = DivT(quot=7, rem=2), c = DivT(quot=9, rem=0)
# a == b
# a != c
