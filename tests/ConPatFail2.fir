type T(a: U32, b: U32, c: U32)

main():
    let x = T(c = u32(1), b = u32(2), a = u32(3))
    match x:
        T(a = a, b = b): ()

# args: --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/ConPatFail2.fir:6:9: Constructor takes named arguments {a, b, c}, but applied {a, b}
