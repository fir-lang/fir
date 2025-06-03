f1[VarRow[r]]() Result[[E1, ..r], ()]
    Result.Err(~E1)

f2[VarRow[r]]() Result[[E1, E2, ..r], ()]
    if Bool.True:
        Result.Err(~E1)
    else:
        Result.Err(~E2)

f3[VarRow[r]]() Result[[E1, E2, ..r], ()]
    let err = if Bool.True:
        ~E1
    else:
        ~E2
    Result.Err(err)

f4() Result[[E1, E2, E3], ()]
    f1()
    f2()
    f3()

f5Simple() Result[[E2, E3], ()]
    match f4():
        Result.Err(errs):
            match errs:
                ~E1: Result.Ok(())
                other: Result.Err(other)

        Result.Ok(()):
            Result.Ok(())

f5Complex() Result[[E2, E3], ()]
    match f4():
        Result.Err(~E1) | Result.Ok(()):
            Result.Ok(())

        Result.Err(other):
            Result.Err(other)

f6[VarRow[errs]](f: Fn() exn Result[[E1, ..errs], ()]) exn Result[[..errs], ()]
    match f():
        Result.Err(~E1) | Result.Ok(()):
            Result.Ok(())

        Result.Err(other):
            Result.Err(other)

# Similar to `f6`, but the call site adds more error cases.
#
# TODO: I'm not sure that this type is right.. Do we need an "absent" constraint
# like `errs \ E1`?
#
# Currently this fails because we try to unify:
#
#   [E1, ..r1] ~ [..errs]
#
# and `E1` cannot be added to `errs` as it's a rigid type variable.
#
# f7[errs](f: Fn() Result[[..errs], ()]) Result[[E1, ..errs], ()]
#     match f():
#         Result.Err(err):
#             Result.Err(err)
#
#         Result.Ok(()):
#             Result.Err(~E1)

f7_2[VarRow[errs]](f: Fn() exn Result[[E1, ..errs], ()]) exn Result[[E1, ..errs], ()]
    match f():
        Result.Err(err):
            Result.Err(err)

        Result.Ok(()):
            Result.Err(~E1)

f7_arg_1() Result[[E1, E2], ()]
    Result.Err(~E1)

f7_arg_2[VarRow[errs]]() Result[[E2, ..errs], ()]
    Result.Err(~E2)

f8(f: Fn() exn1 [E1, E2]) = ()

f9[VarRow[r]]() [E1, ..r] = ~E1

f10[VarRow[r]](f: Fn([E1, E2, ..r]) exn1 ()) = ()

f11(x: [E1, E2, E3]) = ()

type SimpleError:
    Error([A, B, C])
    NotError(I32)

f12(a: SimpleError) Result[[C], I32]
    match a:
        SimpleError.Error(~A | ~B) Result.Err(~C)
        SimpleError.Error(other) Result.Err(other)
        SimpleError.NotError(i) Result.Ok(i)

main()
    # Almost like function subtyping: a function that throws less can be passed
    # as a function that throws more.
    f8(f9)

    # Similar to the above, but for arguments: a function that handles more can
    # be passed as a function that handles less.
    f10(f11)

    f7_2(f7_arg_1)
    f7_2(f7_arg_2)

    ()
