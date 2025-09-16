main() U32:
    123

# args: --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/MainType1.fir:1:1: Unable to unify types
#              U32 and
#              ()
#              (
#                 Con("U32", Star)
#                 Anonymous { labels: {}, extension: None, kind: Record, is_row: false }
#              )
