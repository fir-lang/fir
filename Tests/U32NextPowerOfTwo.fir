main():
    test(0)
    test(1)
    test(2)
    test(3)
    test(4)
    test((u32(1) << 30) + 1)
    test((u32(1) << 31) + 1)
    test(U32.max())


test(x: U32):
    print("`x` --> `x.nextPowerOfTwo()`")

# expected stdout:
# 0 --> 1
# 1 --> 1
# 2 --> 2
# 3 --> 4
# 4 --> 4
# 1073741825 --> 2147483648
# 2147483649 --> 0
# 4294967295 --> 0
