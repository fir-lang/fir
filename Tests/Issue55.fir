main():
    let x = 123
    if Bool.True:
        let x = 456
        printStr(x.toStr())
    printStr(x.toStr())

# expected stdout:
# 456
# 123
