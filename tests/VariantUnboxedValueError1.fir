f() [U32, Bool]:
    ~u32(123)

main():
    f()
    ()

# expected exit status: 101
# expected stderr: tests/VariantUnboxedValueError1.fir:2:5: Unable to resolve pred Boxed[U32]
