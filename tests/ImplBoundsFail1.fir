type A[t]:
    i: t

impl[t1: ToStr, t2] A[t1, t2]:
    test(self)
        printStr(self.i.toStr())

main() = A(i = 123i32).test()

# args: --typecheck --no-backtrace
# expected stderr:
# tests/ImplBoundsFail1.fir:4:21: Incorrect number of type arguments to A, expected 1, found 2
