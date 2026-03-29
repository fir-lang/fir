printRecord[
    RowToList[recRow],
    ToStr[RowToList[recRow].List],
](record: (x: U32, ..recRow)):
    let (x, ..rest) = record
    print("x = `x`")
    print("rest = `RowToList[recRow].rowToList(rest)`")

main():
    printRecord((x = u32(0), y = u32(1), msg = "hi"))

# expected stdout:
# x = 0
# rest = msg = hi -> y = 1 -> []
