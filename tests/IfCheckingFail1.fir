main():
    let x = if Bool.True:
        u32(1)
    else:
        "Hi"

# args: --no-backtrace
# expected exit status: 101
# expected stderr: tests/IfCheckingFail1.fir:5:9: Unable to unify types Str and U32
