f1():
    throw(~A)

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/ExnFail4.fir:2:5: Unable to unify types
#              [A: (), .._2] and
#              ?exn
#              (
#                 Anonymous { labels: {"A": Anonymous { labels: {}, extension: None, kind: Record, is_row: false }}, extension: Some(Var(TyVarRef(TyVar { id: 2, kind: Row(Variant), level: 0, link: None, loc: tests/ExnFail4.fir:2:11-2:13 }))), kind: Variant, is_row: false }
#                 Con("?exn", Star)
#              )
