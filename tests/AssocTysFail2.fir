prim type I32

prim type Str

type A:
    A

trait Test[a]:
    type T
    test(self): T

impl Test for A:
    type T = I32
    test(self): Str
        "hi"

# args: --typecheck --no-prelude --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/AssocTysFail2.fir:14:5: Trait method implementation of test does not match the trait method type
#                                 Trait method type:          [?exn] Fn(A): [..?exn] A.T
#                                 Implementation method type: [?exn] Fn(A): [..?exn] Str
