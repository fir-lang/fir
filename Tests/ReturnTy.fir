type IoError(msg: Str)

type InvalidDigit(char: Char)

type Overflow:
    Overflow

type EmptyInput:
    EmptyInput

readFile(s: Str) Result[[IoError, ..r], Str]:
    Result.Err(~IoError(msg = "unable to read file"))

parseU32(s: Str) Result[[InvalidDigit, Overflow, EmptyInput, ..r], U32]:
    Result.Ok(u32(123))

parseU32FromFile(filePath: Str) Result[[InvalidDigit, Overflow, EmptyInput, IoError, ..r], U32]:
    let fileContents = match readFile(filePath):
        Result.Err(err): return Result.Err(err)
        Result.Ok(contents): contents

    parseU32(fileContents)

main():
    ()
