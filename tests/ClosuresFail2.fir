type Err:
    Err

type Foo:
    Foo

test(f: Fn() U32 / [Err]):
    ()

main():
    test(||: throw(~Foo.Foo))

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/ClosuresFail2.fir:11:14: Unable to unify variant with constructors {"Foo"} with variant with constructors {"Err"}
