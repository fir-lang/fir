type MyNum2 = MyNum
type MyNum = U32

main():
    let x: MyNum2 = 42
    printStr(x.toStr())

# expected stdout:
# 42
