type A:
    A

f1():
    throw(~A.A)

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/ExnFail4.fir:5:5: Unable to unify types
#              [A: A, .._2] and
#              ?exn
#              (
#                 Anonymous { labels: {"A": Con("A", Star)}, extension: Some(Var(TyVarRef(TyVar { id: 2, kind: Row(Variant), level: 0, link: None, loc: tests/ExnFail4.fir:5:11-5:15 }))), kind: Variant, is_row: false }
#                 Con("?exn", Star)
#              )
