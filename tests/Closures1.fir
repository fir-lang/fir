main():
    let c1 = fn() {
        printStr("Hi")
    }

    let val = "captured"

    let c2 = fn() {
        printStr(val)
    }

    c1()
    c2()

    val = "not captured"

    c2 = fn() {
        c2()
        c1()
    }

    c2()

# expected stdout:
# Hi
# captured
# captured
# Hi
