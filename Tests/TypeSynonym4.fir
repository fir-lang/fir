type MyNum = U32
type MyNum2 = MyNum

main():
    let x: MyNum2 = 42
    printStr(x.toStr())

# expected stdout:
# 42
