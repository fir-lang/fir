#[include("sys/time.h", "stdlib.h")]
import [Fir/C as C]


extern type TimeVal = "struct timeval"(
    tvSec: U64 = "tv_sec",
    tvUsec: U64 = "tv_usec",
)


TimeVal.new(sec: U64, usec: U64) TimeVal:
    C/inline("(struct timeval){ .tv_sec = `sec`, .tv_usec = `usec` }")


main():
    let tv: TimeVal = TimeVal.new(1, 2)
    printStr("tvSec = `tv.tvSec`")
    printStr("tvUsec = `tv.tvUsec`")


# expected stdout:
# tvSec = 1
# tvUsec = 2
