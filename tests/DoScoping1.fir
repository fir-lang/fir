main():
    do:
        let x: U32 = 123
    print(x)

# args: --no-backtrace
# expected exit status: 101
# expected stderr: tests/DoScoping1.fir:4:11: Unbound variable x
