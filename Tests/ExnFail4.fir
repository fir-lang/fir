type A:
    A

f1():
    throw(~A.A)

# args: --typecheck
# expected exit status: 101
# expected stderr:
# Tests/ExnFail4.fir:5:5: Unable to unify types
#              [A, .._2] and
#              ?exn
#              (
#                 Variant { labels: {"A": Con("A", Star)}, extension: Some(UVar(UVarRef(UVar { id: 2, kind: Row(Variant), link: None, loc: Tests/ExnFail4.fir:5:11-5:15 }))), is_row: false }
#                 RVar("?exn", Star)
#              )
