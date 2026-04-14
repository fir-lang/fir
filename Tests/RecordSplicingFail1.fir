main():
    let x: U32 = 5
    let r = (a = 1, ..x)
    print(r.a)

# expected exit status: 101
# expected stderr:
# Tests/RecordSplicingFail1.fir:3:23: Unable to unify types
#              U32 and
#              (.._2)
#              (
#                 Con("U32", Star)
#                 Record { labels: {}, extension: Some(UVar(UVarRef(UVar { id: 2, kind: Row(Record), link: None, loc: Tests/RecordSplicingFail1.fir:3:23-3:24 }))), is_row: false }
#              )
