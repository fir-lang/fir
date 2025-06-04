main():
    printStr((0b0000_1111u8 | 0b1111_0000u8 == 0b1111_1111u8).toStr())
    printStr((0xFFu32 | 0xFF00u32 == 0xFFFFu32).toStr())

    # TODO: Add more tests

# expected stdout:
# Bool.True
# Bool.True
