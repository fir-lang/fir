main
    match f():
        Foo.A: ()
        Foo.B: ()

f(): Option[U32] = Option.None

# args: --no-backtrace
# expected exit status: 101
# expected stderr: tests/PatConFail1.fir:3:9: Undefined type Foo
