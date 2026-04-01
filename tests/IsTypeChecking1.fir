expectU32(x: U32):
    ()

foo() Option[U32]:
    Option.None

main():
    expectU32(foo() is Option.None)

# expected exit status: 101
# expected stderr: tests/IsTypeChecking1.fir:8:15: Unable to unify types Bool and U32
