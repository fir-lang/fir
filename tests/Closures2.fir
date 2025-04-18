test(f: Fn(): [Err] U32)
    ()

main
    test({ 123u32 })
    test(fn() { 123u32 })
    test(fn(): U32 { 123 })
    test(fn(): [Err] U32 { 123 })
    test(fn(): [Err] U32 { 123u32 })
