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
# tests/RecordVariantUnificationFail3.fir:11:9: Unable to unify types
#              (a: U32) and
#              [A, B]
#              (
#                 Record { labels: {"a": Con("U32", Star)}, extension: None, is_row: false }
#                 Variant { labels: {"A": Con("A", Star), "B": Con("B", Star)}, extension: None, is_row: false }
#              )
