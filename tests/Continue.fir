testFor(n: I32) I32:
    let sum = i32(0)
    for i: I32 in range(0, n):
        # TODO: Use modulus once we have it.
        if i & 0b1 == 0b1:
            continue
        sum += i
    sum

testWhile(n: I32) I32:
    let sum = i32(0)
    let i = i32(0)
    while Bool.True:
        if i == n:
            break

        # TODO: Use modulus once we have it.
        if i & 0b1 == 0b1:
            i += 1
            continue

        sum += i
        i += 1
    sum

main():
    printStr(testFor(10).toStr())
    printStr(testFor(20).toStr())
    printStr(testWhile(10).toStr())
    printStr(testWhile(20).toStr())

# expected stdout:
# 20
# 90
# 20
# 90
