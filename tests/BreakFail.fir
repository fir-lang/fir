fn main()
    break

# args: --typecheck --no-prelude --no-backtrace
# expected exit status: 101
# expected stderr: tests/BreakFail.fir:2:5: `break` or `continue` statement not inside a loop
