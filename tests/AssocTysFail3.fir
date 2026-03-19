trait Foo[t]:
    type A

prim type U32

prim type U64

impl Foo[U32]:
    type A = U64

test[Foo[t].A = U64]():
    ()

main():
    test[U64, []]()

# args: --typecheck --no-prelude
# expected exit status: 101
# expected stderr:
# Unable to resolve predicates:
# tests/AssocTysFail3.fir:15:5: Foo[U64].A = U64
