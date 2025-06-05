trait Test[t, arg]:
    test(self: t, arg: arg)

impl Test[U32, [FooError]]:
    test(self: U32, arg: [FooError]):
        print(self)

main():
    123u32.test[U32, [FooError], []](~FooError)

# expected stdout: 123
