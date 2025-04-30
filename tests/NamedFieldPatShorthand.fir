type Foo:
    a: U32
    b: U32
    c: U32

main
    let x = Foo(a = 1u32, b = 2u32, c = 3u32)

    match x:
        Foo(a, b, c):
            print("a = `a`, b = `b`, c = `c`")

    match x:
        Foo(c, a, b):
            print("a = `a`, b = `b`, c = `c`")

    match x:
        Foo(b, ..):
            print("b = `b`")

    match x:
        Foo(c = q1, b = q2, a):
            print("a = `a`, q1 = `q1`, q2 = `q2`")

# expected stdout:
# a = 1, b = 2, c = 3
# a = 1, b = 2, c = 3
# b = 2
# a = 1, q1 = 3, q2 = 2
