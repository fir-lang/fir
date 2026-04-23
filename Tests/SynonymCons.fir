type Result1[e, t] = Result[e, t]


type Result2[t] = Result1[Str, t]


type Result3 = Result2[U32]

f1() Result1[Str, U32]:
    Result1.Ok(123)


f2() Result1[Str, U32]:
    Result1.Err("Hi")


f3() Result1[Str, U32]:
    Result1[Str, U32].Ok(123)


f4() Result1[Str, U32]:
    Result1[Str, U32].Err("Hi")


f5() Result2[U32]:
    Result2.Ok(123)


f6() Result2[U32]:
    Result2[U32].Ok(123)


f7() Result2[U32]:
    Result2.Err("Hi")


f8() Result2[U32]:
    Result2[U32].Err("Hi")


f9() Result3:
    Result3.Ok(123)


f10() Result3:
    Result3.Err("Hi")


main():
    # Match `Result1`
    match f1():
        Result.Ok(t): print(t)
        Result.Err(e): print(e)

    match f1():
        Result[Str, U32].Ok(t): print(t)
        Result[Str, U32].Err(e): print(e)

    match f1():
        Result1.Ok(t): print(t)
        Result1.Err(e): print(e)

    match f1():
        Result1[Str, U32].Ok(t): print(t)
        Result1[Str, U32].Err(e): print(e)

    match f1():
        Result2.Ok(t): print(t)
        Result2.Err(e): print(e)

    match f1():
        Result2[U32].Ok(t): print(t)
        Result2[U32].Err(e): print(e)

    match f1():
        Result3.Ok(t): print(t)
        Result3.Err(e): print(e)

    # Match `Result2`
    match f5():
        Result.Ok(t): print(t)
        Result.Err(e): print(e)

    match f5():
        Result[Str, U32].Ok(t): print(t)
        Result[Str, U32].Err(e): print(e)

    match f5():
        Result1.Ok(t): print(t)
        Result1.Err(e): print(e)

    match f5():
        Result1[Str, U32].Ok(t): print(t)
        Result1[Str, U32].Err(e): print(e)

    match f5():
        Result2.Ok(t): print(t)
        Result2.Err(e): print(e)

    match f5():
        Result2[U32].Ok(t): print(t)
        Result2[U32].Err(e): print(e)

    match f5():
        Result3.Ok(t): print(t)
        Result3.Err(e): print(e)

    # Match `Result3`
    match f9():
        Result.Ok(t): print(t)
        Result.Err(e): print(e)

    match f9():
        Result[Str, U32].Ok(t): print(t)
        Result[Str, U32].Err(e): print(e)

    match f9():
        Result1.Ok(t): print(t)
        Result1.Err(e): print(e)

    match f9():
        Result1[Str, U32].Ok(t): print(t)
        Result1[Str, U32].Err(e): print(e)

    match f9():
        Result2.Ok(t): print(t)
        Result2.Err(e): print(e)

    match f9():
        Result2[U32].Ok(t): print(t)
        Result2[U32].Err(e): print(e)

    match f9():
        Result3.Ok(t): print(t)
        Result3.Err(e): print(e)

# args: --typecheck
