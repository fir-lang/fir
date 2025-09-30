main():
    let x: Result[U32] = panic("")

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/PartialTyAppFail1.fir:2:12: Incorrect number of type arguments to Result, expected 2, found 1
