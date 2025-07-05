main():
    printStr((u8(0xFF).asI8()).toStr())
    printStr((u32(0xFFFFFFFF).asI32()).toStr())
    printStr((u32(0xFFFFFFFF).asU8()).toStr())

    # TODO: Add more tests

# expected stdout:
# -1
# -1
# 255
