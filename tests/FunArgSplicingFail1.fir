f(x: U32) U32:
    x + 1

main():
    let args = (x = u32(1))
    print(f(..args))

# expected exit status: 101
# expected stderr:
# tests/FunArgSplicingFail1.fir:6:11: Function with positional arguments can't have a spliced argument
