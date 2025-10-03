type A:
    A

type B:
    B

f1() a / [A]:
    throw(~A.A)

f2() a / [A]:
    throw(~B.B)

# args: --typecheck
# expected exit status: 101
# expected stderr:
# tests/ExnFail2.fir:11:5: Unable to unify variant with constructors {"B"} with variant with constructors {"A"}
