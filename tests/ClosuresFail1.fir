type Err:
    Err

test(f: Fn() U32 / [Err]):
    ()

main():
    test(||: i32(123))

# args: --typecheck
# expected exit status: 101
# expected stderr: tests/ClosuresFail1.fir:8:14: Unable to unify types I32 and U32
