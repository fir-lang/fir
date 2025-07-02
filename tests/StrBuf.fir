main():
    let buf = StrBuf.withCapacity(u32(10))
    buf.push('A')
    printStr(buf.len().toStr())
    printStr(buf._bytes.get(u32(0)).toStr())
    printStr(buf.toStr())
    buf.clear()

    buf.push('é')
    printStr(buf.len().toStr())
    printStr(buf._bytes.get(u32(0)).toStr())
    printStr(buf._bytes.get(u32(1)).toStr())
    printStr(buf.toStr())
    buf.clear()

    buf.push('€')
    printStr(buf.len().toStr())
    printStr(buf._bytes.get(u32(0)).toStr())
    printStr(buf._bytes.get(u32(1)).toStr())
    printStr(buf._bytes.get(u32(2)).toStr())
    printStr(buf.toStr())
    buf.clear()

    buf.push('😀')
    printStr(buf.len().toStr())
    printStr(buf._bytes.get(u32(0)).toStr())
    printStr(buf._bytes.get(u32(1)).toStr())
    printStr(buf._bytes.get(u32(2)).toStr())
    printStr(buf._bytes.get(u32(3)).toStr())
    printStr(buf.toStr())

# expected stdout:
# 1
# 65
# A
# 2
# 195
# 169
# é
# 3
# 226
# 130
# 172
# €
# 4
# 240
# 159
# 152
# 128
# 😀
