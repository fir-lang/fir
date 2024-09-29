fn main() =
    let buf = StrBuf.withCapacity(10u32)
    buf.push('A')
    printStr(buf.len().toStr())
    printStr(buf._bytes.get(0u32).toStr())
    printStr(buf.toStr())
    buf.clear()

    buf.push('é')
    printStr(buf.len().toStr())
    printStr(buf._bytes.get(0u32).toStr())
    printStr(buf._bytes.get(1u32).toStr())
    printStr(buf.toStr())
    buf.clear()

    buf.push('€')
    printStr(buf.len().toStr())
    printStr(buf._bytes.get(0u32).toStr())
    printStr(buf._bytes.get(1u32).toStr())
    printStr(buf._bytes.get(2u32).toStr())
    printStr(buf.toStr())
    buf.clear()

    buf.push('😀')
    printStr(buf.len().toStr())
    printStr(buf._bytes.get(0u32).toStr())
    printStr(buf._bytes.get(1u32).toStr())
    printStr(buf._bytes.get(2u32).toStr())
    printStr(buf._bytes.get(3u32).toStr())
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
