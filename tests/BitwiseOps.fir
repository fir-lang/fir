main():
    printStr((u8(0b0000_1111) | u8(0b1111_0000) == u8(0b1111_1111)).toStr())
    printStr((u32(0xFF) | u32(0xFF00) == u32(0xFFFF)).toStr())

    # TODO: Add more tests

# expected stdout:
# Bool.True
# Bool.True
