f[Boxed[t]](x: t):
    let v = ~x
    ()

main():
    f(u32(123))

# expected exit status: 101
# expected stderr: tests/VariantUnboxedValueError3.fir:6:5: Unable to resolve pred Boxed[U32]
