main():
    let x = match Bool.True:
        Bool.True: u32(1)
        Bool.False: "Hi"

# expected exit status: 101
# expected stderr: tests/MatchCheckingFail1.fir:4:21: Unable to unify types Str and U32
