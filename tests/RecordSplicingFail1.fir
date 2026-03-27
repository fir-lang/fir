main():
    let x: U32 = 5
    let r = (a = 1, ..x)
    print(r.a)

# expected exit status: 101
# expected stderr:
# tests/RecordSplicingFail1.fir:3:23: Unable to unify types
#              U32 and
#              (.._2)
#              (
#                 Con("U32", Star)
#                 Anonymous { labels: {}, extension: Some(UVar(UVarRef(UVar { id: 2, kind: Row(Record), level: 1, link: None, loc: tests/RecordSplicingFail1.fir:3:23-3:24 }))), record_or_variant: Record, is_row: false }
#              )
