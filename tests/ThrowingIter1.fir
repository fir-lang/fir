checkedAdd(i1: U32, i2: U32): Option[U32]
    if i1 > 4294967295u32 - i2:
        return Option.None

    return Option.Some(i1 + i2)

checkedMul(i1: U32, i2: U32): Option[U32]
    let result = i1 * i2

    if i1 != 0 && result / i1 != i2:
        return Option.None

    return Option.Some(result)

parseU32Exn(s: Str): [InvalidDigit, Overflow, EmptyInput, ..r] U32
    if s.len() == 0:
        throw(~EmptyInput)

    let result: U32 = 0

    for c: Char in s.chars():
        if c < '0' || c > '9':
            throw(~InvalidDigit)

        let digit = c.asU32() - '0'.asU32()

        result = match checkedMul(result, 10):
            Option.None: throw(~Overflow)
            Option.Some(newResult): newResult

        result = match checkedAdd(result, digit):
            Option.None: throw(~Overflow)
            Option.Some(newResult): newResult

    result

main()
    let strings: Vec[Str] = Vec.withCapacity(10)
    strings.push("1")
    strings.push("2")
    strings.push("3")
    strings.push("4b")

    let ret = try(fn(): [EmptyInput, InvalidDigit, Overflow] () {
        for x: U32 in strings.iter().map(parseU32Exn):
            printStr(x.toStr())
    })

    match ret:
        Result.Ok(()) | Result.Err(~EmptyInput) | Result.Err(~Overflow): printStr("WAT")
        Result.Err(~InvalidDigit): printStr("OK")

# expected stdout:
# 1
# 2
# 3
# OK
