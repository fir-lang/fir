type Foo(a: U32, b: U32, c: U32)

main():
    let x = Foo(a = u32(1), b = u32(2), c = u32(3))

    match x:
        Foo(a = x, ..):
            print(x)

    match x:
        Foo(b = x, ..):
            print(x)

    match x:
        Foo(c = x, ..):
            print(x)

    match x:
        Foo(b = x, a = y, ..):
            print(x + y)

    match x:
        Foo(c = x, a = y, ..):
            print(x + y)

    match x:
        Foo(c = x, b = y, ..):
            print(x + y)

# expected stdout:
# 1
# 2
# 3
# 3
# 4
# 5
