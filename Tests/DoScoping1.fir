main():
    do:
        let x: U32 = 123
    print(x)

# expected exit status: 101
# expected stderr: Tests/DoScoping1.fir:4:11: Unbound name x
