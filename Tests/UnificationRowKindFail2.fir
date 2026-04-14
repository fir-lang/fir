type Test[recRowRec](
    record: (..recRowRec),
)

main():
    let x: Test[(a: U32)] = Test(record = (a = u32(123)))

# args: --typecheck
# expected exit status: 101
# expected stderr:
# Tests/UnificationRowKindFail2.fir:6:29: Unable to unify types _0 and (a: U32) (kind mismatch, Row[Rec] ~ *)
