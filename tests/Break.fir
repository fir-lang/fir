testFor(n: I32) I32:
    let sum = i32(0)
    for i: I32 in range(0, 10000):
        if sum > 100:
            break
        sum += i
    sum

testWhile(n: I32) I32:
    let sum = i32(0)
    let i = i32(0)
    while Bool.True:
        if sum > 100:
            break
        sum += i
        i += 1
    sum

main():
    printStr(testFor(10).toStr())
    printStr(testFor(20).toStr())
    printStr(testWhile(10).toStr())
    printStr(testWhile(20).toStr())

# expected stdout:
# 105
# 105
# 105
# 105
