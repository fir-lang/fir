test() U32: u32(123)

main():
    match test():
        idx: ()

    printStr("`idx`")

# expected exit status: 101
# expected stderr: tests/MatchTcBug.fir:7:16: Unbound variable idx
