#[include("sys/time.h", "stdlib.h")]
import [Fir/C as C]


extern "sys/time.h" type TimeVal = "struct timeval"(
    tvSec: I64 = "tv_sec",
    tvUsec: I64 = "tv_usec",
)


allocTimeVal() CPtr[TimeVal]:
    C/inline("calloc(1, sizeof(struct timeval))")


freeTimeVal(tv: CPtr[TimeVal]):
    C/inline("free(`tv`)")


main():
    let tv = allocTimeVal()
    if tv.isNull():
        panic("calloc failed")

    tv.tvSec = i64(12345)
    tv.tvUsec = i64(678)

    printStr("tvSec = `tv.tvSec`")
    printStr("tvUsec = `tv.tvUsec`")

    tv.tvSec = i64(99999)
    printStr("tvSec after overwrite = `tv.tvSec`")

    freeTimeVal(tv)


# expected stdout:
# tvSec = 12345
# tvUsec = 678
# tvSec after overwrite = 99999
