type Err:
    Err

type Foo:
    Foo

test(f: Fn() U32 / [Err]):
    ()

main():
    test(\(): throw(~Foo.Foo))

# args: --typecheck
# expected exit status: 101
# expected stderr: tests/ClosuresFail2.fir:11:15: Unable to unify [Foo, .._3] with [Err]
