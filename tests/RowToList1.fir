printRecord[
    RowToList[recRow],
    TypeLevelListToStr[RowToList[recRow].List],
](record: (x: U32, ..recRow)):
    let (x, ..rest) = record
    print("x = `x`")
    print("rest = `RowToList[recRow].rowToList(rest).typeLevelListToStr()`")

main():
    printRecord((x = u32(0), y = u32(1), msg = "hi"))
