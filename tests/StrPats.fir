main()
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

    match "aOK":
        "a" _: printStr("a matched")
        _: panic("")

    match "asdf":
        "asdf" _: printStr("asdf matched")
        _: panic("")

# expected stdout:
# OK
# OK
# Bool.True
# a matched
# asdf matched
