main():
    let x: [] = ()

# expected exit status: 101
# expected stderr:
# Tests/RecordVariantUnificationFail1.fir:2:17: Unable to unify types
#              () and
#              []
#              (
#                 Record { labels: {}, extension: None, is_row: false }
#                 Variant { labels: {}, extension: None, is_row: false }
#              )
