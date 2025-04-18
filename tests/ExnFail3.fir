f1(): [..r] a
    throw(~A)

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/ExnFail3.fir:2:5: Unable to unify variant with constructors {"A"} with variant with constructors {}
