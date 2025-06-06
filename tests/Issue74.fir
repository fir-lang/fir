main():
    let iter = range(Bool.True, Bool.False)
    iter.next[RangeIterator[Bool], Bool, []]()
    ()

# args: --no-backtrace
# expected exit status: 101
# expected stderr:
# Unable to resolve predicates:
# tests/Issue74.fir:3:5: Ord[Bool]
# tests/Issue74.fir:3:5: Step[Bool]
