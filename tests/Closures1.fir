main():
    let c1 = ||:
        printStr("Hi")

    let val = "captured"

    let c2 = ||:
        printStr(val)

    c1()
    c2()

    val = "not captured"

    c2 = ||:
        c2()
        c1()

    c2()

# expected stdout:
# Hi
# captured
# captured
# Hi
