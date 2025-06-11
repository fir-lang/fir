type Err:
    Err

test(f: Fn() U32 / [Err]):
    ()

main():
    test({ 123i32 })

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr: tests/ClosuresFail1.fir:8:12: Unable to unify types I32 and U32
