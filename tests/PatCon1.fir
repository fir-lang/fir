main():
    match f():
        Foo(a, b):
            print(a)
            print(b)

type Foo:
    a: U32
    b: U32

f() Foo = Foo(a = 1, b = 2)

# expected stdout:
# 1
# 2
