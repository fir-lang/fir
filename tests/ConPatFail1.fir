type T:
    a: U32
    b: U32
    c: U32

main
    let x = T(c = 1u32, b = 2u32, a = 3u32)
    match x:
        T(a = a, b = b, c = c, d = d): ()

# args: --no-backtrace
# expected exit status: 101
# expected stderr: tests/ConPatFail1.fir:9:9: Constructor doesn't take named argument 'd'
