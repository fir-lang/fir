test() U32 = 123u32

main():
    match test():
        idx: ()

    printStr("`idx`")

# args: --no-backtrace
# expected exit status: 101
# expected stderr: tests/MatchTcBug.fir:7:16: Unbound variable idx
