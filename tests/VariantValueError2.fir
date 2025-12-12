f(x: t):
    let v = ~x
    ()

main(): ()

# expected exit status: 101
# expected stderr: tests/VariantValueError2.fir:2:13: Type in variant is not a constructor: t
