main():
    let x = ~u32(123)
    ()

# expected exit status: 101
# expected stderr:
# tests/VariantValueError1.fir:2:13: Integers can't be made variants in the interpreter
