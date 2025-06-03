type T:
    a: U32
    b: U32
    c: U32

main():
    let x = T(c = 1u32, b = 2u32, a = 3u32)
    match x:
        T(b = a, b = b) ()

# args: --no-backtrace
# expected exit status: 101
# expected stderr: tests/ConPatFail3.fir:9:9: Named argument 'b' applied multiple times
