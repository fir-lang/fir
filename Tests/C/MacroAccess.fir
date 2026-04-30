#[include("time.h")]
import [Fir/C as C]


monotonicClockId() C/Int:
    C/inline("CLOCK_MONOTONIC")


main():
    let _ = monotonicClockId()
    printStr("OK")


# expected stdout:
# OK
