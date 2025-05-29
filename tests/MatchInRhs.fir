test(arg: Result[U32, U32]): U32
    let x = 123u32

    x = match arg:
        Result.Ok(val): val
        Result.Err(err): return err

    x

main()
    printStr(test(Result.Ok(10u32)).toStr())
    printStr(test(Result.Err(10u32)).toStr())

# expected stdout:
# 10
# 10
