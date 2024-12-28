fn test[R](r: (x: I32, y: I32, ..R)) =
    printStr(r.x.toStr())
    printStr(r.y.toStr())

fn main() =
    test((x = 123))

# args: --typecheck --no-backtrace
# expected stderr:
# tests/RowsFail1.fir:6:10: Unable to unify records with keys {"x"} with record with keys {"x", "y"}
