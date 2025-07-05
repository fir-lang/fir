main():
    printNoNl("Calling f... ")
    match try(f):
        Result.Ok(()): print("OK")
        Result.Err(~FooError.FooError): print("FooError")
        Result.Err(~AssertionError.AssertionError): print("AssertError")

    printNoNl("Calling g... ")
    match try(g):
        Result.Ok(()): print("OK")
        Result.Err(~FooError.FooError): print("FooError")
        Result.Err(~AssertionError.AssertionError): print("AssertionError")

    g()

f() / [FooError, ..exn]:
    throw(~FooError.FooError)

g():
    throwUnchecked(~AssertionError.AssertionError)

type FooError:
    FooError

type AssertionError:
    AssertionError

# args: --no-backtrace
# expected exit status: 101
# expected stdout:
# Calling f... FooError
# Calling g... AssertionError

# expected stderr:
# tests/ThrowUnchecked.fir:3:5: Unexhaustive pattern match
# tests/ThrowUnchecked.fir:9:5: Unexhaustive pattern match
# Uncaught exception
