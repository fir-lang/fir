type MyUnit

main():
    let unit = MyUnit()

# args: --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/UnitProductInvocationFail.fir:4:16: Function in function application is not a function: Con("MyUnit", Star)
