type Test[recRowRec]:
    record: (..recRowRec)

main
    let x: Test[(a: U32)] = Test(record = (a = 123u32))

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/UnificationRowKindFail2.fir:5:29: Unable to unify var with kind row(record) with type with kind *
