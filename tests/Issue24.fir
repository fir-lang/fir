type A[t]:
    i: t

A.test[ToStr[t1]](self: A[t1]): printStr(self.i.toStr())

main(): A(i = i32(123)).test()

# expected stdout: 123
