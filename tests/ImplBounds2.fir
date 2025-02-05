type A[t]:
    i: t

A.test[ToStr[t1], Eq[t2]](self: A[t1], t2: t2)
    printStr(self.i.toStr())
    printStr((t2 == t2).toStr())

main() = A(i = 123i32).test(456u32)

# args: --typecheck --no-backtrace
