main():
    let x: [Option[U32], Bool] = ~Bool.False
    x.y = 123

# expected exit status: 101
# expected stderr:
# Tests/AssignFail1.fir:3:5: Type [Option[U32], Bool] doesn't have fields that can be assigned
