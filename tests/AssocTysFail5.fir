trait Foo[t]:
    type A

    getA() Foo[t].A

prim type U32

prim type U64

impl Foo[U32]:
    type A = U64

    getA() Foo[U32].A:
        u64(123)

u64(x: U64) U64: x

main():
    let x: U32 = Foo.getA[U32, []]()
    ()

# args: --typecheck --no-prelude
# expected exit status: 101
# expected stderr: tests/AssocTysFail5.fir:19:18: Unable to unify types U64 and U32
