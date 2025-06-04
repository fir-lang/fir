type T:
    a: U32

T.captureSelf(self: T) (Fn() () / [..errs]):
    fn() () / [..errs] {
        printStr(self.a.toStr())
    }

main() = T(a = 123).captureSelf()()

# expected stdout: 123
