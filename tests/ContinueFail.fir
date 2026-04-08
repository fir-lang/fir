#[NoImplicitPrelude]
import []

main():
    continue

# args: --typecheck
# expected exit status: 101
# expected stderr: tests/ContinueFail.fir:5:5: `break` or `continue` statement not inside a loop
