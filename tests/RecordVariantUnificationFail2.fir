type A(Str)

main():
    let x: (a: Str) = ~A("hi")

# expected exit status: 101
# expected stderr:
# tests/RecordVariantUnificationFail2.fir:4:23: Unable to unify types
#              [A, .._0] and
#              (a: Str)
#              (
#                 Anonymous { labels: {"A": Con("A", Star)}, extension: Some(UVar(UVarRef(UVar { id: 0, kind: Row(Variant), level: 1, link: None, loc: tests/RecordVariantUnificationFail2.fir:4:23-4:31 }))), record_or_variant: Variant, is_row: false }
#                 Anonymous { labels: {"a": Con("Str", Star)}, extension: None, record_or_variant: Record, is_row: false }
#              )
