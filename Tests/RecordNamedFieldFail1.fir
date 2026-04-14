main():
    let (z, x) = f()
    print("x = `x`, y = `y`, z = `z`")

f() (x: U32, y: U32, z: U32): (x = u32(123), y = u32(456), z = u32(789))

# expected exit status: 101
# expected stderr:
# Tests/RecordNamedFieldFail1.fir:2:9: Unable to unify (x: U32, z: U32) with (x: U32, y: U32, z: U32)
