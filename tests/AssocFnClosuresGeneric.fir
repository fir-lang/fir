type T:
    i: I32

T.print1[a: ToStr](self, other: a)
    printStr("T(i = `self.i`, other = `other.toStr()`)")

T.print2[a](self)
    printStr("T(i = `self.i`)")

main()
    let f1 = T(i = 1).print1
    f1("hi")

    let f2 = T(i = 2).print2
    f2()

# expected stdout:
# T(i = 1, other = hi)
# T(i = 2)
