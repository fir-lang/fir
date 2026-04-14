test[Eq[t], ToStr[t]](a: t):
    printStr((a == a).toStr())
    printStr(a.toStr())

type A[t](i: t)

A.test[Eq[t], ToStr[t]](self: A[t]):
    printStr((self.i == self.i).toStr())
    printStr(self.i.toStr())

main():
    test(i32(123))
    test(u32(456))

# expected stdout:
# Bool.True
# 123
# Bool.True
# 456
