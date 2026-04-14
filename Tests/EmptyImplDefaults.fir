trait Foo[t]:
    test(self: t) t:
        self

impl Foo[U32]

main():
    print(u32(123).test())

# expected stdout: 123
