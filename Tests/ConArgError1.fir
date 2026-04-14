#[NoImplicitPrelude]
import []

type T:
    T1

main():
    match T.T1:
        T.T1(_): ()

# args: --typecheck
# expected exit status: 101
# expected stderr:
# Tests/ConArgError1.fir:9:9: Type T doesn't take arguments, but applied 1 arguments
