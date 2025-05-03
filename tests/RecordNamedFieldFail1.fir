main
    let (z, x) = f()
    print("x = `x`, y = `y`, z = `z`")

f: (x: U32, y: U32, z: U32) = (x = 123u32, y = 456u32, z = 789u32)

# args: --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/RecordNamedFieldFail1.fir:2:9: Unable to unify record with fields {"x", "z"} with record with fields {"x", "y", "z"}
