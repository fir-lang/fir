trait Foo[t]:
    type A

prim type U32

prim type U64

impl Foo[U32]:
    type A = U64

impl Foo[U64]:
    type A = U32

test[Foo[t].A = U64]():
    ()

main():
    test[U64, []]()

# args: --typecheck --no-prelude
# expected exit status: 101
# expected stderr: tests/AssocTysFail4.fir:18:5: Unable to unify types U64 and U32
