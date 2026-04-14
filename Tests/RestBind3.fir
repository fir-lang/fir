type Foo(
    x: U32,
    y: Bool,
    z: Str,
)

foo() Foo:
    Foo(x = 1, y = Bool.True, z = "hi")

main():
    let Foo(x, ..rest) = foo()
    print(x)
    print(rest.y)
    print(rest.z)

# expected stdout:
# 1
# Bool.True
# hi
