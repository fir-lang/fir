type Foo[recRow](
    x: Bool,
    ..recRow
)

foo[r: Row[Rec]](rec: Foo[r]):
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
#                 Record { labels: {"y": Con("Str", Star)}, extension: Some(UVar(UVarRef(UVar { id: 1, kind: Row(Record), link: None, loc: tests/ProductExtensionPatFail3.fir:8:9-8:41 }))), is_row: true }
#                 RVar("r", Row(Record))
#              )
