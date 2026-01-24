# `Rem` not implemented for 16 and 64 bit integers yet.

main():
    print("I8:")
    print(u8(3).rem(u8(2)))
    print(i8(3).rem(i8(2)))
    print(i8(-3).rem(i8(2)))
    print(i8(-3).rem(i8(-2)))
    print(i8(3).rem(i8(-2)))

    print("")
    print("I32:")
    print(u32(3).rem(u32(2)))
    print(i32(3).rem(i32(2)))
    print(i32(-3).rem(i32(2)))
    print(i32(-3).rem(i32(-2)))
    print(i32(3).rem(i32(-2)))

# expected stdout:
# I8:
# 1
# 1
# -1
# -1
# 1
# 
# I32:
# 1
# 1
# -1
# -1
# 1
