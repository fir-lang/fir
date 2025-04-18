# Code for the blog post: https://osa1.net/posts/2025-01-18-fir-error-handling.html
#
# TODO: Enable overflow tests after adding operators that allow overflows.

parseU32(s: Str): Result[[InvalidDigit, Overflow, EmptyInput, ..r], U32]
    if s.len() == 0:
        return Result.Err(~EmptyInput)

    let result: U32 = 0

    for c: Char in s.chars():
        if c < '0' || c > '9':
            return Result.Err(~InvalidDigit)

        let digit = c.asU32() - '0'.asU32()

        result = match checkedMul(result, 10):
            Option.None: return Result.Err(~Overflow)
            Option.Some(newResult): newResult

        result = match checkedAdd(result, digit):
            Option.None: return Result.Err(~Overflow)
            Option.Some(newResult): newResult

    Result.Ok(result)

checkedAdd(i1: U32, i2: U32): Option[U32]
    if i1 > 4294967295u32 - i2:
        return Option.None

    return Option.Some(i1 + i2)

checkedMul(i1: U32, i2: U32): Option[U32]
    let result = i1 * i2

    if i1 != 0 && result / i1 != i2:
        return Option.None

    return Option.Some(result)

parseIntErrorToStr(error: [InvalidDigit, Overflow, EmptyInput]): Str
    match error:
        ~InvalidDigit: "invalid digit"
        ~Overflow: "overflow"
        ~EmptyInput: "empty input"

defaultEmptyInput(res: Result[[EmptyInput, ..r], U32]): Result[[..r], U32]
    match res:
        Result.Err(~EmptyInput): Result.Ok(0u32)
        Result.Err(other): Result.Err(other)
        Result.Ok(val): Result.Ok(val)

readFile(s: Str): Result[[IoError, ..r], Str]
    # We don't have the standard library support for file IO yet, just return
    # an error for now.
    Result.Err(~IoError)

parseU32FromFile(filePath: Str): Result[[InvalidDigit, Overflow, EmptyInput, IoError, ..r], U32]
    let fileContents = match readFile(filePath):
        Result.Err(err): return Result.Err(err)
        Result.Ok(contents): contents

    parseU32(fileContents)

parseWith(vec: Vec[Str], parseFn: Fn(Str): Result[errs, a]): Result[errs, Vec[a]]
    let ret = Vec.withCapacity(vec.len())

    for s: Str in vec.iter():
        match parseFn(s):
            Result.Err(err): return Result.Err(err)
            Result.Ok(val): ret.push(val)

    Result.Ok(ret)

parseWith2(vec: Vec[Str], parseFn: Fn(Str): Result[[OtherError, ..r], a]): Result[[..r], Vec[a]]
    let ret = Vec.withCapacity(vec.len())

    for s in vec.iter():
        match parseFn(s):
            Result.Err(~OtherError): continue
            Result.Err(err): return Result.Err(err)
            Result.Ok(val): ret.push(val)

    Result.Ok(ret)

handleSomeErrs(error: [Overflow, OtherError]): U32 = 0

parseWithErrorHandler(input: Str, handler: Fn([Overflow, ..r1]): U32): Result[[InvalidDigit, EmptyInput, ..r2], U32]
    match parseU32(input):
        Result.Err(~Overflow): Result.Ok(handler(~Overflow))
        Result.Err(other): Result.Err(other)
        Result.Ok(val): Result.Ok(val)

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

readFileExn(s: Str): [IoError, ..r] Str
    # We don't have the standard library support for file IO yet, just return
    # an error for now.
    throw(~IoError)

parseU32FromFileExn(filePath: Str): [InvalidDigit, Overflow, EmptyInput, IoError, ..r] U32
    parseU32Exn(readFileExn(filePath))

parseWithExn(vec: Vec[Str], parseFn: Fn(Str): exn a): exn Vec[a]
    let ret = Vec.withCapacity(vec.len())
    for s in vec.iter():
        ret.push(parseFn(s))
    ret

parseU32UsingExnVersion(s: Str): Result[[InvalidDigit, Overflow, EmptyInput, ..r], U32]
    try({ parseU32Exn(s) })

parseU32UsingResultVersion(s: Str): [InvalidDigit, Overflow, EmptyInput, ..r] U32
    untry(parseU32(s))

main
    printStr("----- parseU32")
    printStr(parseU32("123").mapErr(parseIntErrorToStr).toStr())
    printStr(parseU32("12a3").mapErr(parseIntErrorToStr).toStr())
    printStr(parseU32("").mapErr(parseIntErrorToStr).toStr())
    # printStr(parseU32("100000000000000000000000").mapErr(parseIntErrorToStr).toStr())
    printStr("")

    printStr("----- parseU32FromFile")
    match parseU32FromFile("test"):
        Result.Err(~IoError): printStr("io error")
        Result.Err(other): printStr(parseIntErrorToStr(other))
        Result.Ok(val): printStr(val.toStr())
    printStr("")

    printStr("----- parseWith")
    let vec: Vec[Str] = Vec.withCapacity(3)
    vec.push("1")
    vec.push("2")
    vec.push("3")
    printStr(parseWith(vec, parseU32).mapErr(parseIntErrorToStr).toStr())
    vec.push("blah")
    printStr(parseWith(vec, parseU32).mapErr(parseIntErrorToStr).toStr())
    printStr("")

    printStr("----- parseWithErrorHandler")
    printStr(parseWithErrorHandler("123", handleSomeErrs).mapErr(parseIntErrorToStr).toStr())
    # printStr(parseWithErrorHandler("10000000000000000000000", handleSomeErrs).mapErr(parseIntErrorToStr).toStr())
    printStr("")

    printStr("----- parseU32UsingExnVersion")
    printStr(parseU32UsingExnVersion("123").mapErr(parseIntErrorToStr).toStr())
    printStr(parseU32UsingExnVersion("12a3").mapErr(parseIntErrorToStr).toStr())
    printStr(parseU32UsingExnVersion("").mapErr(parseIntErrorToStr).toStr())
    # printStr(parseU32UsingExnVersion("100000000000000000000000").mapErr(parseIntErrorToStr).toStr())

# expected stdout:
# ----- parseU32
# Result.Ok(123)
# Result.Err(invalid digit)
# Result.Err(empty input)
# 
# ----- parseU32FromFile
# io error
# 
# ----- parseWith
# Result.Ok([1,2,3])
# Result.Err(invalid digit)
# 
# ----- parseWithErrorHandler
# Result.Ok(123)
# 
# ----- parseU32UsingExnVersion
# Result.Ok(123)
# Result.Err(invalid digit)
# Result.Err(empty input)
