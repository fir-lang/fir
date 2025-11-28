test() Str / U32:
    throw(u32(123))

main():
    printStr(try(test).toStr())

    let x: Result[U32, U32] = try(\(): throw(u32(456)))
    printStr(x.toStr())

# expected stdout:
# Result.Err(123)
# Result.Err(456)
