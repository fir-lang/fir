type Foo[extras](
    x: U32,
    y: U32,
    ..extras
)

main():
    let foo = Foo(x = 123, y = 456, z = "hi")
    print(foo.x)
    print(foo.y)
    print(foo.z)
    foo.x += 1
    foo.y *= 2
    foo.z = "bye"
    print(foo.x)
    print(foo.y)
    print(foo.z)

# expected stdout:
# 123
# 456
# hi
# 124
# 912
# bye
