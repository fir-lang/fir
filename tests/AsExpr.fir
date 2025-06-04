main():
    printStr((0xFFu8.asI8()).toStr())
    printStr((0xFFFFFFFFu32.asI32()).toStr())
    printStr((0xFFFFFFFFu32.asU8()).toStr())

    # TODO: Add more tests

# expected stdout:
# -1
# -1
# 255
