type A:
    A

f1():
    throw(~A.A)

# args: --typecheck
# expected exit status: 101
# expected stderr:
# tests/ExnFail4.fir:5:5: Unable to unify types
#              [A, .._2] and
#              ?exn
#              (
#                 Anonymous { labels: {"A": Con("A", Star)}, extension: Some(UVar(UVarRef(UVar { id: 2, kind: Row(Variant), link: None, loc: tests/ExnFail4.fir:5:11-5:15 }))), record_or_variant: Variant, is_row: false }
#                 RVar("?exn", Star)
#              )
