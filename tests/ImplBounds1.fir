type A[t]:
    i: t

A.test[ToStr[t1]](self: A[t1]):
    printStr(self.i.toStr())

main() = A(i = i32(123)).test()

# TODO(24) We can't run this program as the monomorphiser cannot handle renamed type parameters.
# args: --typecheck --no-backtrace
