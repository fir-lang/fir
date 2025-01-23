type A[t]:
    i: t


A[t1: ToStr].test[t2: Eq](self, t2: t2)
    printStr(self.i.toStr())
    printStr((t2 == t2).toStr())

main() = A(i = 123i32).test(456u32)

# args: --typecheck --no-backtrace
