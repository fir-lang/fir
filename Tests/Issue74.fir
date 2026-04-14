main():
    let iter = range(Bool.True, Bool.False)
    iter.next[RangeIterator[Bool], []]()
    ()

# expected exit status: 101
# expected stderr:
# Unable to resolve predicates:
# Tests/Issue74.fir:3:5: Step[Bool]
# Tests/Issue74.fir:3:5: Ord[Bool]
