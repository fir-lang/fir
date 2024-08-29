prim type I32

prim type Str

type A:
    A

trait Test[A]:
    type T
    fn test(self): T

impl Test[A]:
    type T = I32
    fn test(self): Str =
        "hi"

# args: --typecheck --no-prelude --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/AssocTysFail2.fir:14:5: Trait method implementation of test does not match the trait method type
#                                 Trait method type:          Fn(A): T
#                                 Implementation method type: Fn(A): Str

