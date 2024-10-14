type A[T]:
    i: T

impl[T1: ToStr] A[T1]:
    fn test[T2: Eq](self, t2: T2) =
        printStr(self.i.toStr())
        printStr((t2 == t2).toStr())

fn main() = A(i = 123i32).test(456u32)

# args: --typecheck --no-backtrace
