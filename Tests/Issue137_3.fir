type FooError:
    FooError

trait Test[t, exn]:
    test(self: t) / exn

impl Test[U32, [FooError, ..exn]]:
    test(self: U32) / [FooError, ..exn]:
        print(self)

main():
    match try(\(): u32(123).test[U32, [FooError]]()):
        Result.Ok(()): print("OK")
        Result.Err(~FooError.FooError): print("FooError")

# expected stdout:
# 123
# OK
