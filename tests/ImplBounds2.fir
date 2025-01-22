type A[t]:
    i: t


A.test[t1: ToStr, t2: Eq](self: A[t1], t2: t2)
    printStr(self.i.toStr())
    printStr((t2 == t2).toStr())

main() = A(i = 123i32).test(456u32)

# args: --typecheck --no-backtrace
