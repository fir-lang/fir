test() U32 Str
    throw(123u32)

main()
    printStr(try(test).toStr())

    let x: Result[U32, U32] = try({ throw(456u32) })
    printStr(x.toStr())

# expected stdout:
# Result.Err(123)
# Result.Err(456)
