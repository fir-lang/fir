test(r: (x: I32, y: I32, ..r)) (x: I32, y: I32):
    printStr(r.x.toStr())
    printStr(r.y.toStr())
    r

main():
    test((x = 123, y = 456))

# args: --typecheck
# expected exit status: 101
# expected stderr:
# tests/RowsFail2.fir:4:5: Unable to unify types
#              r and
#              row()
#              (
#                 RVar("r", Row(Record))
#                 Record { labels: {}, extension: None, is_row: true }
#              )
