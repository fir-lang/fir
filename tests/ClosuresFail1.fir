test(f: Fn(): [Err] U32)
    ()

main
    test({ 123i32 })

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr: tests/ClosuresFail1.fir:5:10: Unable to unify types I32 and U32
