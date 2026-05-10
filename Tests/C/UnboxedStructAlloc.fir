#[include("sys/time.h", "stdlib.h")]
import [Fir/C as C]


extern type TimeVal = "struct timeval"(
    tvSec: U64 = "tv_sec",
    tvUsec: U64 = "tv_usec",
)


TimeVal.new(sec: U64, usec: U64) TimeVal:
    C/inline("(struct timeval){ .tv_sec = `sec`, .tv_usec = `usec` }")


main():
    let tv1: TimeVal = TimeVal.new(1, 2)
    printStr("tvSec = `tv1.tvSec`")
    printStr("tvUsec = `tv1.tvUsec`")

    let tv2: TimeVal = TimeVal(tvSec = 3, tvUsec = 4)
    printStr("tvSec = `tv2.tvSec`")
    printStr("tvUsec = `tv2.tvUsec`")


# expected stdout:
# tvSec = 1
# tvUsec = 2
# tvSec = 3
# tvUsec = 4
