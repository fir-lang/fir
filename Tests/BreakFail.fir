#[NoImplicitPrelude]
import []

main():
    break

# args: --typecheck
# expected exit status: 101
# expected stderr: Tests/BreakFail.fir:5:5: `break` or `continue` statement not inside a loop
