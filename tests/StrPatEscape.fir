main
    let s = "\""
    printStr(s)

    match s:
        "\"" rest:
            printStr("Matched, rest = \"`rest`\"")
        other:
            panic("")

    match s:
        "\"":
            printStr("Matched")
        other:
            panic("")

# expected stdout:
# "
# Matched, rest = ""
# Matched
