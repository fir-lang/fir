trait Foo[a, errs1]:
    foo(self: a) () / [..errs1]

impl Foo[U32, errs2]:
    foo(self: U32) () / [..errs2]:
        printStr("Hi")

main(): u32(123).foo()

# expected stdout: Hi
