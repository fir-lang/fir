test: U32 Str
    throw(123u32)

main = printStr(try(test).toStr())

# expected stdout: Result.Err(123)
