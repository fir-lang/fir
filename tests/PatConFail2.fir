main()
    match f():
        Foo.A: ()
        Foo.B: ()

type Foo:
    X
    Y

f(): Option[U32] = Option.None

# args: --no-backtrace
# expected exit status: 101
# expected stderr: tests/PatConFail2.fir:3:9: Type Foo does not have a constructor named A
