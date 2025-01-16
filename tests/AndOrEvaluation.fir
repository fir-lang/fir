main()
    if Bool.True || panic("FAIL 1"):
        printStr("OK 1")

    if Bool.False && panic("FAIL 2"):
        panic("FAIL 3")

    printStr("OK 2")

# expected stdout:
# OK 1
# OK 2
