type Foo[extras: Row[Rec]](
    x: U32,
    y: U32,
    msg: Str,
    ..extras
)

foo() Foo[row(z: U32)]:
    Foo(x = 1, y = 2, msg = "hi", z = u32(3))

main():
    let Foo(x, ..rest) = foo()
    print(x)
    print(rest.y)
    print(rest.z)
    print(rest.msg)

# expected stdout:
# 1
# 2
# 3
# hi
