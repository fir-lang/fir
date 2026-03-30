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
#                 Anonymous { labels: {"a": Con("U32", Star)}, extension: None, record_or_variant: Record, is_row: false }
#                 Anonymous { labels: {"A": Con("A", Star), "B": Con("B", Star)}, extension: None, record_or_variant: Variant, is_row: false }
#              )
