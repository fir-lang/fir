fn main() =
    let x = if Bool.True:
        (x = 123i32)
    else:
        (y = "hi")
    ()

# args: --typecheck --no-backtrace
# expected stderr:
# tests/RowsFail3.fir:2:13: Unable to unify records with keys {"x"} with record with keys {"y"}
