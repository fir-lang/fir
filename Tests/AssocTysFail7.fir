# Test that an impl cannot define an associated type not declared in the trait.

trait Foo[t]:
    type A

impl Foo[U32]:
    type A = U64
    type B = U32

main():
    ()

# expected exit status: 101
# expected stderr: Tests/AssocTysFail7.fir:8:10: Trait Foo does not have associated type B
