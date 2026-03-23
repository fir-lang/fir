trait Foo[t]:
    type A

prim type U32

prim type U64

impl Foo[U32]:
    type A = U64
    type A = U32

# args: --typecheck --no-prelude
# expected exit status: 101
# expected stderr: tests/AssocTysFail2.fir:10:10: Associated type A implemented mutiple times
