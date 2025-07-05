main():
    let x = if Bool.True:
        (x = i32(123))
    else:
        (y = "hi")
    ()

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/RowsFail3.fir:5:9: Unable to unify record with fields {"y"} with record with fields {"x"}
