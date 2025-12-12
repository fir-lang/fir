f(x: t):
    let v = ~x
    ()

main(): ()

# expected exit status: 101
# expected stderr: tests/VariantUnboxedValueError2.fir:2:13: Unable to resolve pred Boxed[t]
