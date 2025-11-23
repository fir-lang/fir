id(x: t) t: x

main():
    let x = id[U32, []]
    print(x(123))

    let y = x[U32]
    print(y(456))

# expected exit status: 101
# expected stderr:
# tests/LocalTyArgsFail.fir:7:13: Local variables can't have type parameters, but `x` is passed type arguments
