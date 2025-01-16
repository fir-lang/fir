type A[t]:
    i: t

impl[t1: ToStr] A[t1]:
    test[t2: Eq](self, t2: t2)
        printStr(self.i.toStr())
        printStr((t2 == t2).toStr())

main() = A(i = 123i32).test(456u32)

# args: --typecheck --no-backtrace
