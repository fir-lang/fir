type A[t]:
    i: t

A.test[ToStr[t1]](self: A[t1]) = printStr(self.i.toStr())

main() = A(i = 123i32).test()

# expected stdout: 123
