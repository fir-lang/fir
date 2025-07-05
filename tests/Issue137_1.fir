type FooError:
    FooError

trait Test[t, arg]:
    test(self: t, arg: arg)

impl Test[U32, [FooError]]:
    test(self: U32, arg: [FooError]):
        print(self)

main():
    u32(123).test[U32, [FooError], []](~FooError.FooError)

# expected stdout: 123
