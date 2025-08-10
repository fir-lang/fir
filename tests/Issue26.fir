trait A[t1]:
    a(self: t1)

trait B[t2]:
    b(self: t2)

type Box[t3](thing: t3)

impl[A[t4]] B[Box[t4]]:
    b(self: Box[t4]):
        printStr("In b")

main():
    Box(thing = u32(123)).b()

# args: --no-backtrace
# expected exit status: 101
# expected stderr: tests/Issue26.fir:14:5: Unable to resolve pred A[U32]
