#[include("stdlib.h")]
import [Fir/C as C]


extern type DivT = "div_t"(
    quot: I32 = "quot",
    rem: I32 = "rem",
)


mkDivOnHeap(num: I32, den: I32) C/Ptr[DivT]:
    C/inline("({ div_t* p = (div_t*)malloc(sizeof(div_t)); *p = div(`num`, `den`); p; })")


freeDivT(p: C/Ptr[DivT]) / exn:
    C/inline[C/Void, exn]("free(`p`)")
    ()


main():
    let p = mkDivOnHeap(17, 5)
    printStr("field:  quot = `p.quot`, rem = `p.rem`")

    let DivT(quot, rem) = p.deref()
    printStr("let:    quot = `quot`, rem = `rem`")

    match p.deref():
        DivT(quot, rem):
            printStr("match:  quot = `quot`, rem = `rem`")

    freeDivT(p)


# expected stdout:
# field:  quot = 3, rem = 2
# let:    quot = 3, rem = 2
# match:  quot = 3, rem = 2
