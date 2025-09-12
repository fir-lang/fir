main():
    print("".trimAscii())
    print("a".trimAscii())
    print(" a".trimAscii())
    print(" a ".trimAscii())
    print(" a ".trimAscii().len())
    print(" \n\t\ra\n\t\r ".trimAscii())
    print(" \n\t\ra\n\t\r ".trimAscii().len())

# expected stdout:
# a
# a
# a
# 1
# a
# 1
