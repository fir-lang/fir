fn test[r](r: (x: I32, y: I32, ..r)): (x: I32, y: I32) =
    printStr(r.x.toStr())
    printStr(r.y.toStr())
    r

fn main() =
    test((x = 123, y = 456))

# args: --typecheck --no-backtrace
# expected stderr:
# tests/RowsFail2.fir:4:5: Unable to unify types
#              r and
#              row()
#              (
#                 Con("r")
#                 Anonymous { labels: {}, extension: None, kind: Record, is_row: true }
#              )
