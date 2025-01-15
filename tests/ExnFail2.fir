fn f1(): {A}
    throw(~A)

fn f2(): {A}
    throw(~B)

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/ExnFail2.fir:5:5: Unable to unify variant with constructors {"B"} with variant with constructors {"A"}
