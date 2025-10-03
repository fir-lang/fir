type T:
    T1

main():
    match T.T1:
        T.T1(_): ()

# expected exit status: 101
# expected stderr:
# tests/ConArgError.fir:6:9: Constructor doesn't take arguments, but applied 1 arguments
