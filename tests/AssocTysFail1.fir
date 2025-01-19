prim type I32

type A:
    A

trait Test[a]:
    type T
    test(self): T

impl Test for A:
    type T = I32
    test(self): T
        "hi"

# args: --typecheck --no-prelude --no-backtrace
# expected stderr: tests/AssocTysFail1.fir:13:9: Unable to unify types Str and I32
