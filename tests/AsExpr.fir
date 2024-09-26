fn main() =
    printStr((0xFFu8 as I8).toStr())
    printStr((0xFFFFFFFFu32 as I32).toStr())
    printStr((0xFFFFFFFFu32 as U8).toStr())

    # TODO: Add more tests

# expected stdout:
# -1
# -1
# 255
