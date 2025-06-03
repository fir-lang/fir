main()
    match f():
        Foo.X: ()

type Foo:
    a: U32
    b: U32

f() Foo = Foo(a = 1, b = 2)

# args: --no-backtrace
# expected exit status: 101
# expected stderr: tests/PatConFail3.fir:3:9: Type Foo is not a sum type
