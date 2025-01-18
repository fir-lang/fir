readFile(s: Str): Result[[IoError, ..r], Str]
    Result.Err(~IoError)

parseU32(s: Str): Result[[InvalidDigit, Overflow, EmptyInput, ..r], U32]
    Result.Ok(123u32)

parseU32FromFile(filePath: Str): Result[[InvalidDigit, Overflow, EmptyInput, IoError, ..r], U32]
    let fileContents = match readFile(filePath):
        Result.Err(err): return Result.Err(err)
        Result.Ok(contents): contents

    parseU32(fileContents)

main
    ()
