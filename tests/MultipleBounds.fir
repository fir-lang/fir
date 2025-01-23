test[t: Eq + ToStr](a: t)
    printStr((a == a).toStr())
    printStr(a.toStr())

type A[t]:
    i: t

A[t: Eq + ToStr].test(self)
    printStr((self.i == self.i).toStr())
    printStr(self.i.toStr())

main()
    test(123i32)
    test(456u32)

# expected stdout:
# Bool.True
# 123
# Bool.True
# 456
