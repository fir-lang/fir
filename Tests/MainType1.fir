main() U32:
    123

# expected exit status: 101
# expected stderr:
# Tests/MainType1.fir:1:1: Unable to unify types
#              U32 and
#              ()
#              (
#                 Con("U32", Star)
#                 Record { labels: {}, extension: None, is_row: false }
#              )
