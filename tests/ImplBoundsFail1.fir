type A[t]:
    i: t

A.test[ToStr[t1]](self: A[t1, t2])
    printStr(self.i.toStr())

main() = A(i = 123i32).test()

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/ImplBoundsFail1.fir:4:25: Incorrect number of type arguments to A, expected 1, found 2
