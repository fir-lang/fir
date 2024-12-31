fn main() =
    let x = if Bool.True:
        (x = 123i32)
    else:
        (y = "hi")
    ()

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/RowsFail3.fir:2:13: Unable to unify record with fields {"x"} with record with fields {"y"}

