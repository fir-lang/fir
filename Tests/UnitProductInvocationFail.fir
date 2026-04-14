type MyUnit

main():
    let unit = MyUnit()

# expected exit status: 101
# expected stderr:
# Tests/UnitProductInvocationFail.fir:4:16: Function in function application is not a function: Con("MyUnit", Star)
