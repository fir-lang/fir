main():
    let a = Vec.withCapacity(u32(10))
    let b = a.withCapacity

# args: --typecheck
# expected exit status: 101
# expected stderr:
# tests/AssocFnSelectFail.fir:3:13: Type Vec[_1] does not have field or method withCapacity
