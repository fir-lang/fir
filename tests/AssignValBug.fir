main():
    let a: U32 = 0
    # TODO: Assignments are not expressions, so we need an indented block here in the function
    # expression body.
    let x: Result[Str, ()] = try(\():
        a += 1
    )
    match x:
        Result.Err(err): print(err)
        Result.Ok(()): print(a)

# expected stdout: 0
