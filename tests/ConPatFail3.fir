type T(a: U32, b: U32, c: U32)

main():
    let x = T(c = u32(1), b = u32(2), a = u32(3))
    match x:
        T(b = a, b = b): ()

# expected exit status: 101
# expected stderr: tests/ConPatFail3.fir:6:9: Named argument 'b' applied multiple times
