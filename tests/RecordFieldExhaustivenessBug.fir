main():
    match f():
        Option.None:
            print("WAT")
        Option.Some((a, ..)):
            print(a)

    match g():
        Option.None:
            print("WAT")
        Option.Some((a = Result.Ok(i), ..)):
            print(i)

    match g():
        Option.None:
            print("WAT")
        Option.Some((a = Result.Ok(i), ..)):
            print(i)
        Option.Some((a = Result.Err(i), ..)):
            print(i)

f() Option[(a: U32, b: U32)]:
    Option.Some((a = 1, b = 2))

g() Option[(a: Result[U32, U32], b: U32)]:
    Option.Some((a = Result.Ok(123), b = 456))

# expected stdout:
# 1
# 123
# 123

# expected stderr: tests/RecordFieldExhaustivenessBug.fir:8:5: Unexhaustive pattern match
