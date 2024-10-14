type A[T]:
    i: T

impl[T1: ToStr] A[T1]:
    fn test(self) =
        printStr(self.i.toStr())

fn main() = A(i = 123i32).test()

# TODO(24): We can't run this program as the monomorphiser cannot handle renamed type parameters.
# args: --typecheck --no-backtrace
