type A[T]:
    i: T

impl[T1: ToStr] A[T1]:
    fn test(self) =
        printStr(self.i.toStr())

fn main() = A(i = 123i32).test()
