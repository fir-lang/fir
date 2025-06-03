main():
    let a: U32 = 0
    let x: Result[Str, ()] = try({
        a += 1
    })
    match x:
        Result.Err(err) print(err)
        Result.Ok(()) print(a)

# expected stdout: 0
