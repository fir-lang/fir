type A:
    A

f1() a / [..r]:
    throw(~A.A)

# args: --typecheck
# expected exit status: 101
# expected stderr:
# tests/ExnFail3.fir:5:5: Unable to unify variant with constructors {"A"} with variant with constructors {}
