prim type I32

type A:
    A

trait Test[A]:
    type T
    fn test(self): T

impl Test[A]:
    type T = I32
    fn test(self): T =
        "hi"

# args: --typecheck --no-prelude --no-backtrace
# expected stderr: Unable to unify types Str and I32 at tests/AssocTysFail1.fir:13:9
