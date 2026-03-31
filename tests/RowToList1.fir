printRecord[
    RecRowToList[recRow],
    ToStr[RecRowToList[recRow].List],
](record: (x: U32, ..recRow)):
    let (x, ..rest) = record
    print("x = `x`")
    print("rest = `RecRowToList[recRow].rowToList(rest)`")
    print("full = `(x = x, ..rest)`")

main():
    printRecord((x = u32(0), y = u32(1), msg = "hi"))

# expected stdout:
# x = 0
# rest = Option.Some(msg = hi, y = 1)
# full = (msg = hi, x = 0, y = 1)
