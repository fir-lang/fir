type A(Str)

main():
    let x: (a: Str) = ~A("hi")

# expected exit status: 101
# expected stderr:
# Tests/RecordVariantUnificationFail2.fir:4:23: Unable to unify types
#              [A, .._0] and
#              (a: Str)
#              (
#                 Variant { labels: {"A": Con("A", Star)}, extension: Some(UVar(UVarRef(UVar { id: 0, kind: Row(Variant), link: None, loc: Tests/RecordVariantUnificationFail2.fir:4:23-4:31 }))), is_row: false }
#                 Record { labels: {"a": Con("Str", Star)}, extension: None, is_row: false }
#              )
