type Foo(x: U32)

Fo.f(self: Foo):
    print("Foo.f")

main():
    let a = Foo(x = u32(123))
    a.f()

# expected exit status: 101
# expected stderr: tests/AssocFnParentNameCheck.fir:3:1: Unknown type Fo
