test(arg: Result[U32, U32]) U32:
    let x = u32(123)

    x = match arg:
        Result.Ok(val): val
        Result.Err(err): return err

    x

main():
    printStr(test(Result.Ok(u32(10))).toStr())
    printStr(test(Result.Err(u32(10))).toStr())

# expected stdout:
# 10
# 10
