type T:
    x: U32

T.increment(self) T:
    T(x = self.x + 1)

impl ToStr[T]:
    toStr(self: T) Str:
        "T(x = `self.x.toStr()`)"

main():
    let s = T(x = 123)
        .increment()
        .increment()
        .increment()
        .increment()
        .toStr()
    printStr(s)

# expected stdout: T(x = 127)
