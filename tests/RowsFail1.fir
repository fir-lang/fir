fn test[R](r: (x: I32, y: I32, ..R)) =
    printStr(r.x.toStr())
    printStr(r.y.toStr())

fn main() =
    test((x = 123))

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/RowsFail1.fir:6:10: Unable to unify record with fields {"x"} with record with fields {"x", "y"}

