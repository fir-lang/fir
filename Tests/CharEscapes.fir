main():
    let buf = StrBuf.withCapacity(10)
    buf.push('\'')
    buf.push('\n')
    buf.push('\t')
    buf.push('\r')
    buf.push('\\')
    printStr(buf._bytes.get(0).toStr())
    printStr(buf._bytes.get(1).toStr())
    printStr(buf._bytes.get(2).toStr())
    printStr(buf._bytes.get(3).toStr())
    printStr(buf._bytes.get(4).toStr())

# expected stdout:
# 39
# 10
# 9
# 13
# 92
