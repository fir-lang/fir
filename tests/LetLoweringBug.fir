main()
    let x: U32 = 123
    printStr(x.toStr())
    let x = x
    printStr(x.toStr())

# expected stdout:
# 123
# 123
