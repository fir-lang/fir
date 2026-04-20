main():
    match f():
        Foo.X: ()

type Foo(a: U32, b: U32)

f() Foo: Foo(a = 1, b = 2)

# expected exit status: 101
# expected stderr: Tests/PatConFail3.fir:3:9: Type Foo does not have sum constructors
