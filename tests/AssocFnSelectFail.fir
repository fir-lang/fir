main()
    let a = Vec.withCapacity(10u32)
    let b = a.withCapacity

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/AssocFnSelectFail.fir:3:13: Type Vec[_2] does not have field or method withCapacity
