foo(x: [A, B]):
    ()

main():
    foo((a = 123u32))

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/RecordVariantUnificationError.fir:5:9: Unable to unify record (a: U32) with variant [A: (), B: ()]
