type T

type A[t](i: t)

A.test[ToStr[t1]](self: A[t1]):
    printStr(self.i.toStr())

main(): A(i = T).test()

# args: --typecheck
# expected exit status: 101
# expected stderr:
# Unable to resolve predicates:
# tests/ImplBoundsFail1.fir:8:9: ToStr[T]
