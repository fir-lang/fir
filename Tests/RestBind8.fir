type Foo(
    x: U32,
    y: Bool,
    z: Str,
)

main():
    let f = Foo(x = 1, y = Bool.True, z = "hi")
    match f:
        Foo(x, ..rest):
            print(x)
            print(rest.y)
            print(rest.z)

# expected stdout:
# 1
# Bool.True
# hi
