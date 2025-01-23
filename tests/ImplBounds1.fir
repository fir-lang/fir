type A[t]:
    i: t

A[t1: ToStr].test(self)
    printStr(self.i.toStr())

main() = A(i = 123i32).test()

# TODO(24): We can't run this program as the monomorphiser cannot handle renamed type parameters.
# args: --typecheck --no-backtrace
