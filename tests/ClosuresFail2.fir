test(f: Fn(): [Err] U32)
    ()

main
    test(fn() { throw(~Foo) })

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/ClosuresFail2.fir:5:10: Unable to unify variant with constructors {"Foo"} with variant with constructors {"Err"}
