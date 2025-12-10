type A:
    A

type B:
    B

foo(x: [A, B]):
    ()

main():
    foo((a = u32(123)))

# args: --typecheck
# expected exit status: 101
# expected stderr:
# tests/RecordVariantUnificationError.fir:11:9: Unable to unify record (a: U32) with variant [A, B]
