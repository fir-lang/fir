type Foo = row(x: I32, y: I32)

makeFoo() (z: I32, ..Foo):
    (x = 1, y = 2, z = 3)

main():
    let foo = makeFoo()
    print(foo.x)
    print(foo.y)
    print(foo.z)

# expected stdout:
# 1
# 2
# 3
