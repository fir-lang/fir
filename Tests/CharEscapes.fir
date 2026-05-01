main():
    let buf = StrBuf.withCapacity(10)
    buf.push('\\')
    buf.push('`')
    buf.push('"')
    buf.push('\'')
    buf.push('\n')
    buf.push('\t')
    buf.push('\r')
    buf.push('\0')
    for char in buf.toStr().chars():
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
