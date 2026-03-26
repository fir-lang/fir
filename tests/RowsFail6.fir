test() (x: U32, ..U32):
    panic("")

# args: --typecheck
# expected exit status: 101
# expected stderr: tests/RowsFail6.fir:1:19: Record extension type U32 has kind *
