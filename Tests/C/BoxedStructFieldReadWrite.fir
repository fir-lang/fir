#[include("sys/time.h", "stdlib.h")]
import [Fir/C as C]


extern type TimeVal = "struct timeval"(
    tvSec: I64 = "tv_sec",
    tvUsec: I64 = "tv_usec",
)


allocTimeVal() C/Ptr[TimeVal]:
    C/inline("calloc(1, sizeof(struct timeval))")


freeTimeVal(tv: C/Ptr[TimeVal]):
    C/inline("free(`tv`)")


main():
    let tv = allocTimeVal()
    if tv.isNull():
        panic("calloc failed")

    tv.tvSec = 12345
    tv.tvUsec = 678

    printStr("tvSec = `tv.tvSec`")
    printStr("tvUsec = `tv.tvUsec`")

    tv.tvSec = 99999
    printStr("tvSec after overwrite = `tv.tvSec`")

    freeTimeVal(tv)


# expected stdout:
# tvSec = 12345
# tvUsec = 678
# tvSec after overwrite = 99999
