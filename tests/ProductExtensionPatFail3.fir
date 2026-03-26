type Foo[recRow](
    x: Bool,
    ..recRow
)

foo[RecRow[r]](rec: Foo[r]):
    match rec:
        Foo(x = Bool.True, y = "hi", ..):
            print("true")

# args: --typecheck
# expected exit status: 101
# expected stderr:
# tests/ProductExtensionPatFail3.fir:8:9: Unable to unify types
#              row(y: Str, .._1) and
#              r
#              (
#                 Anonymous { labels: {"y": Con("Str", Star)}, extension: Some(UVar(UVarRef(UVar { id: 1, kind: Row(Record), level: 0, link: None, loc: tests/ProductExtensionPatFail3.fir:8:9-8:41 }))), record_or_variant: Record, is_row: true }
#                 RVar("r", Row(Record))
#              )
