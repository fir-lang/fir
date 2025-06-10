type Err:
    Err

test(f: Fn() U32 / [Err]):
    ()

main():
    test({ 123u32 })
    test(fn() { 123u32 })
    test(fn() U32 { 123 })
    test(fn() U32 / [Err] { 123 })
    test(fn() U32 / [Err] { 123u32 })
