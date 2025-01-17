main()
    printStr("asdf".startsWith("a").toStr())
    printStr("asdf".startsWith("as").toStr())
    printStr("asdf".startsWith("asd").toStr())
    printStr("asdf".startsWith("asdf").toStr())
    printStr("asdf".startsWith("asdfg").toStr())
    printStr("asdf".charAt(0).toStr())
    printStr("asdf".charAt(1).toStr())
    printStr("asdf".charAt(2).toStr())
    printStr("asdf".charAt(3).toStr())

    let s = " αあ💩"
    printStr(s.charAt(1).toStr())
    printStr(s.charAt(3).toStr())
    printStr(s.charAt(6).toStr())

    printStr("---")

    for char in s.chars():
        printStr(char.toStr())

    for charIdx in s.charIndices():
        let char = charIdx.char
        let idx = charIdx.idx
        printStr("`idx.toStr()`: `char.toStr()`")

    printStr("---")

    let charIter = s.chars()
    printStr(charIter.asStr())
    charIter.next()
    printStr(charIter.asStr())
    charIter.next()
    printStr(charIter.asStr())
    charIter.next()
    printStr(charIter.asStr())
    charIter.next()

    printStr("---")

    # goldentests ignores trailing empty lines, so add some noise to the last empty lines.
    printStr("\"`charIter.asStr()`\"")
    charIter.next()
    printStr("\"`charIter.asStr()`\"")

# expected stdout:
# Bool.True
# Bool.True
# Bool.True
# Bool.True
# Bool.False
# 'a'
# 's'
# 'd'
# 'f'
# 'α'
# 'あ'
# '💩'
# ---
# ' '
# 'α'
# 'あ'
# '💩'
# 0: ' '
# 1: 'α'
# 3: 'あ'
# 6: '💩'
# ---
#  αあ💩
# αあ💩
# あ💩
# 💩
# ---
# \"\"
# \"\"
