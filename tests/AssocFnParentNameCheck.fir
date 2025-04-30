type Foo:
    x: U32

Fo.f(self: Foo)
    print("Foo.f")

main
    let a = Foo(x = 123u32)
    a.f()

# args: --no-backtrace
# expected exit status: 101
# expected stderr: tests/AssocFnParentNameCheck.fir:4:1: Unknown type Fo
