type A:
    A

f1() () / []:
    throw(~A.A)

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/ExnFail1.fir:5:5: Unable to unify variant with constructors {"A"} with variant with constructors {}
