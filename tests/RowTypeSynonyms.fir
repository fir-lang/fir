type Foo = row(x: I32, y: I32)

makeFoo() (..Foo):
    (x = 1, y = 2)

main():
    let foo = makeFoo()
    print(foo.x)
    print(foo.y)

# expected stdout:
# 1
# 2
