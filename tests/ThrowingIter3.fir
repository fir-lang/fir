type EmptyInput:
    EmptyInput

type InvalidDigit:
    InvalidDigit

type Overflow:
    Overflow

checkedAdd(i1: U32, i2: U32) Option[U32]:
    if i1 > u32(4294967295) - i2:
        return Option.None

    return Option.Some(i1 + i2)

checkedMul(i1: U32, i2: U32) Option[U32]:
    let result = i1 * i2

    if i1 != 0 and result / i1 != i2:
        return Option.None

    return Option.Some(result)

parseU32Exn(s: Str) U32 / [InvalidDigit, Overflow, EmptyInput, ..r]:
    if s.len() == 0:
        throw(~EmptyInput.EmptyInput)

    let result: U32 = 0

    for c: Char in s.chars():
        if c < '0' or c > '9':
            throw(~InvalidDigit.InvalidDigit)

        let digit = c.asU32() - '0'.asU32()

        result = match checkedMul(result, 10):
            Option.None: throw(~Overflow.Overflow)
            Option.Some(newResult): newResult

        result = match checkedAdd(result, digit):
            Option.None: throw(~Overflow.Overflow)
            Option.Some(newResult): newResult

    result

handleInvalidDigit(parseResult: Result[[InvalidDigit, ..errs], Option[U32]]) Option[U32] / [..errs]:
    match parseResult:
        Result.Ok(result): result
        Result.Err(~InvalidDigit.InvalidDigit): Option.Some(u32(0))
        Result.Err(other): throw(other)

main():
    let strings: Vec[Str] = Vec.withCapacity(10)
    strings.push("1")
    strings.push("2")
    strings.push("3")
    strings.push("4b")
    strings.push("")

    for x: Result[[Overflow, EmptyInput], U32] in strings.iter().map(parseU32Exn).mapResult(handleInvalidDigit).try():
        match x:
            Result.Err(~Overflow.Overflow): printStr("Overflow")
            Result.Err(~EmptyInput.EmptyInput): printStr("EmptyInput")
            Result.Ok(val): printStr(val.toStr())

parseSumHandleInvalidDigitsLogRest(nums: Vec[Str]) U32:
    let result: U32 = 0
    for i: Result[[Overflow, EmptyInput], U32] in nums.iter().map(parseU32Exn).mapResult(handleInvalidDigit).try():
        match i:
            Result.Err(~Overflow.Overflow): printStr("Overflow")
            Result.Err(~EmptyInput.EmptyInput): printStr("Empty input")
            Result.Ok(i): result += i
    result

# expected stdout:
# 1
# 2
# 3
# 0
# EmptyInput
