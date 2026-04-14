type Err:
    Err

test(f: Fn() U32 / [Err]):
    ()

main():
    test(\(): u32(123))
    test(\() U32: u32(123))
    test(\() U32 / [Err]: 123)
    test(\() U32 / [Err]: u32(123))
