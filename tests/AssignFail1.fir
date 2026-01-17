main():
    let x: [Option[U32], Bool] = ~Bool.False
    x.y = 123

# expected exit status: 101
# expected stderr:
# tests/AssignFail1.fir:3:5: Type [Bool, ..row[Option[U32], ..row[]]] doesn't have fields that can be assigned
