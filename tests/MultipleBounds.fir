fn test[T: Eq + ToStr](a: T) =
    printStr((a == a).toStr())
    printStr(a.toStr())

type A[T]:
    i: T

impl[T: Eq + ToStr] A[T]:
    fn test(self) =
        printStr((self.i == self.i).toStr())
        printStr(self.i.toStr())

fn main() =
    test(123i32)
    test(456u32)

# expected stdout:
# Bool.True
# 123
# Bool.True
# 456
