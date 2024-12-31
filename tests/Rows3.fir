fn f1[R](): Result[[E1, ..R], ()] =
    Result.Err(`E1)

fn f2[R](): Result[[E1, E2, ..R], ()] =
    if Bool.True:
        Result.Err(`E1)
    else:
        Result.Err(`E2)

fn f3[R](): Result[[E1, E2, ..R], ()] =
    let err = if Bool.True:
        `E1
    else:
        `E2
    Result.Err(err)

fn f4(): Result[[E1, E2, E3], ()] =
    f1()
    f2()
    f3()

# TODO: Type refinement
# fn f5(): Result[[E2, E3], ()] =
#     match f4():
#         Result.Err(`E1) | Result.Ok(()):
#             Result.Ok(())
#
#         Result.Err(other):
#             Result.Err(other) # type of `other` should be refined as `[E2, E3]`

# TODO: Type refinement, function expressions
# fn f6[Errs](f: Fn(): Result[[E1, ..Errs], ()]): Result[[..Errs], ()] =
#     match f():
#         Result.Err(`E1) | Result.Ok(()):
#             Result.Ok(())
#
#         Result.Err(other):
#             Result.Err(other)

# Similar to `f6`, but the call site adds more error cases.
# fn f7[Errs](f: Fn(): Result[[..Errs], ()]): Result[[E1, ..Errs], ()] =
#     match f():
#         Result.Err(err):
#             Result.Err
#
#         Result.Ok(()):
#             Result.Err(`E1)

fn f8(f: Fn(): [E1, E2]) = ()

fn f9[R](): [E1, ..R] = `E1

fn f10[R](f: Fn([E1, E2, ..R]): ()) = ()

fn f11(x: [E1, E2, E3]) = ()

fn main() =
    # Almost like function subtyping: a function that throws less can be passed
    # as a function that throws more.
    f8(f9)

    # Similar to the above, but for arguments: a function that handles more can
    # be passed as a function that handles less.
    f10(f11)

    ()
