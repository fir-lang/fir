fn f1[r](): Result[[E1, ..r], ()] =
    Result.Err(`E1)

fn f2[r](): Result[[E1, E2, ..r], ()] =
    if Bool.True:
        Result.Err(`E1)
    else:
        Result.Err(`E2)

fn f3[r](): Result[[E1, E2, ..r], ()] =
    let err = if Bool.True:
        `E1
    else:
        `E2
    Result.Err(err)

fn f4(): Result[[E1, E2, E3], ()] =
    f1()
    f2()
    f3()

fn f5Simple(): Result[[E2, E3], ()] =
    match f4():
        Result.Err(errs):
            match errs:
                `E1: Result.Ok(())
                other: Result.Err(other)

        Result.Ok(()):
            Result.Ok(())

fn f5Complex(): Result[[E2, E3], ()] =
    match f4():
        Result.Err(`E1) | Result.Ok(()):
            Result.Ok(())

        Result.Err(other):
            Result.Err(other)

fn f6[errs](f: Fn(): Result[[E1, ..errs], ()]): Result[[..errs], ()] =
    match f():
        Result.Err(`E1) | Result.Ok(()):
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
# fn f7[errs](f: Fn(): Result[[..errs], ()]): Result[[E1, ..errs], ()] =
#     match f():
#         Result.Err(err):
#             Result.Err(err)
#
#         Result.Ok(()):
#             Result.Err(`E1)

fn f7_2[errs](f: Fn(): Result[[E1, ..errs], ()]): Result[[E1, ..errs], ()] =
    match f():
        Result.Err(err):
            Result.Err(err)

        Result.Ok(()):
            Result.Err(`E1)

fn f7_arg_1(): Result[[E1, E2], ()] =
    Result.Err(`E1)

fn f7_arg_2[errs](): Result[[E2, ..errs], ()] =
    Result.Err(`E2)

fn f8(f: Fn(): [E1, E2]) = ()

fn f9[r](): [E1, ..r] = `E1

fn f10[r](f: Fn([E1, E2, ..r]): ()) = ()

fn f11(x: [E1, E2, E3]) = ()

type SimpleError:
    Error([A, B, C])
    NotError(I32)

fn f12(a: SimpleError): Result[[C], I32] =
    match a:
        SimpleError.Error(`A | `B): Result.Err(`C)
        SimpleError.Error(other): Result.Err(other)
        SimpleError.NotError(i): Result.Ok(i)

fn main() =
    # Almost like function subtyping: a function that throws less can be passed
    # as a function that throws more.
    f8(f9)

    # Similar to the above, but for arguments: a function that handles more can
    # be passed as a function that handles less.
    f10(f11)

    f7_2(f7_arg_1)
    f7_2(f7_arg_2)

    ()
