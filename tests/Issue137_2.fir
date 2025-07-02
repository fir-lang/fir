type FooError:
    FooError

trait Test[t, exn]:
    test(self: t, arg: exn)

impl Test[U32, [FooError, ..exn1]]:
    test(self: U32, arg: [FooError, ..exn1]):
        print(self)

main():
    u32(123).test(~FooError.FooError)

# expected stdout: 123
