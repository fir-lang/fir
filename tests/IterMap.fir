main():
    let sum = u32(0)
    for x: U32 in "1 2 3".splitWhitespace().map(parseU32):
        sum += x
    printStr(sum.toStr())

parseU32(s: Str) U32:
    let result: U32 = 0

    for c: Char in s.chars():
        let digit = c.asU32() - '0'.asU32()
        result *= 10
        result += digit

    result

# expected stdout: 6
