main():
    print("U8:")
    print(U8.min())
    print(U8.max())

    print("")
    print("I8:")
    print(I8.min())
    print(I8.max())

    print("")
    print("U32:")
    print(U32.min())
    print(U32.max())

    print("")
    print("I32:")
    print(I32.min())
    print(I32.max())

    print("")
    print("U64:")
    print(U64.min())
    print(U64.max())

    print("")
    print("I64:")
    print(I64.min())
    print(I64.max())

# expected stdout:
# U8:
# 0
# 255
# 
# I8:
# -128
# 127
# 
# U32:
# 0
# 4294967295
# 
# I32:
# -2147483648
# 2147483647
# 
# U64:
# 0
# 18446744073709551615
# 
# I64:
# -9223372036854775808
# 9223372036854775807
