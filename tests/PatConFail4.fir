main():
    match f():
        Foo: ()

type Foo

f() Foo: panic("")

# args: --no-backtrace
# expected exit status: 101
# expected stderr: tests/PatConFail4.fir:3:9: Type Foo doesn't have any constructors
