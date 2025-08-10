type Test[recRowRec](
    record: (..recRowRec),
)

main():
    let x: Test[(a: U32)] = Test(record = (a = u32(123)))

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/UnificationRowKindFail2.fir:6:29: Unable to unify var with kind row(record) with type with kind *
