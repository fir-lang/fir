type A[T]:
    i: T

impl[T1: ToStr, T2] A[T1, T2]:
    fn test(self) =
        printStr(self.i.toStr())

fn main() = A(i = 123i32).test()

# args: --typecheck --no-backtrace
# expected stderr:
# tests/ImplBoundsFail1.fir:4:21: Incorrect number of type arguments to A, expected 1, found 2
