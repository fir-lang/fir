fn main()
    match "test":
        "asdf": panic("")
        "test": printStr("OK")
        _: panic("")

    match "aOK":
        "a" rest: printStr(rest)
        _: panic("")

    match "asdf":
        "asdf" rest: printStr(rest.isEmpty().toStr())
        _: panic("")

# expected stdout:
# OK
# OK
# Bool.True
