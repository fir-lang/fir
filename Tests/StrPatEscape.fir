main():
    let s = "\""
    printStr(s)

    match s:
        "\"":
            printStr("Matched")
        other:
            panic("")

# expected stdout:
# "
# Matched
