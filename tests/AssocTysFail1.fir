trait Foo[t]:
    type A
    type A

# args: --typecheck --no-prelude
# expected exit status: 101
# expected stderr: tests/AssocTysFail1.fir:3:10: Associated type A declared multiple times
