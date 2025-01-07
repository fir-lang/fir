type A[t]:
    i: t

impl[t1: ToStr] A[t1]:
    fn test(self)
        printStr(self.i.toStr())

fn main() = A(i = 123i32).test()

# TODO(24): We can't run this program as the monomorphiser cannot handle renamed type parameters.
# args: --typecheck --no-backtrace
