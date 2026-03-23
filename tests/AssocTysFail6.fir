# Test that an impl must define all associated types declared in the trait.

trait Foo[t]:
    type A
    type B

impl Foo[U32]:
    type A = U64

main():
    ()

# expected exit status: 101
# expected stderr: tests/AssocTysFail6.fir:7:1: Associated types missing: ["B"]
