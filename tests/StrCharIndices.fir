main()
    let s = " αあ💩"
    printStr("|`s`")
    for charIdx: (char: Char, idx: U32) in s.charIndices():
        let char = charIdx.char
        let idx = charIdx.idx
        printStr("`idx.toStr()`: `char.toStr()`")

    let substr = s.substr(1, s.len())
    printStr("|`substr`")
    for charIdx: (char: Char, idx: U32) in substr.charIndices():
        let char = charIdx.char
        let idx = charIdx.idx
        printStr("`idx.toStr()`: `char.toStr()`")

# expected stdout:
# | αあ💩
# 0: ' '
# 1: 'α'
# 3: 'あ'
# 6: '💩'
# |αあ💩
# 0: 'α'
# 2: 'あ'
# 5: '💩'
