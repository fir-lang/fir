type Err:
    Err

test(f: Fn() U32 / [Err]):
    ()

main():
    test(||: 123u32)
    test(|| U32: 123u32)
    test(|| U32 / [Err]: 123)
    test(|| U32 / [Err]: 123u32)
