fn testFor(n: I32): I32 =
    let sum = 0i32
    for i in range(0, 10000):
        if sum > 100:
            break
        sum += i
    sum

fn testWhile(n: I32): I32 =
    let sum = 0i32
    let i = 0i32
    while Bool.True:
        if sum > 100:
            break
        sum += i
        i += 1
    sum

fn main() =
    printStr(testFor(10).toStr())
    printStr(testFor(20).toStr())
    printStr(testWhile(10).toStr())
    printStr(testWhile(20).toStr())

# expected stdout:
# 105
# 105
# 105
# 105

