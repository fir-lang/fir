main():
    for char in "\\ \` \" ' \n \t \r \0".chars():
        if char == ' ':
            continue
        print(char.asU32())


# expected stdout:
# 92
# 96
# 34
# 39
# 10
# 9
# 13
# 0
