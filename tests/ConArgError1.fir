type T:
    T1

main():
    match T.T1:
        T.T1(_): ()

# args: --typecheck --no-prelude
# expected exit status: 101
# expected stderr:
# tests/ConArgError1.fir:6:9: Type T doesn't take arugments, but applied 1 arguments
