main():
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

    let substr = s.substr(1, s.len())
    printStr(substr.charAt(0).toStr())
    printStr(substr.charAt(2).toStr())
    printStr(substr.charAt(5).toStr())

    printStr("---")

    for char: Char in s.chars():
        printStr(char.toStr())

    printStr("---")

    let charIter = s.chars()
    printStr(charIter.asStr())
    let _: Option[Char] = charIter.next()
    printStr(charIter.asStr())
    let _: Option[Char] = charIter.next()
    printStr(charIter.asStr())
    let _: Option[Char] = charIter.next()
    printStr(charIter.asStr())
    let _: Option[Char] = charIter.next()

    printStr("---")

    # goldentests ignores trailing empty lines, so add some noise to the last empty lines.
    printStr("\"`charIter.asStr()`\"")
    let _: Option[Char] = charIter.next()
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
# 'α'
# 'あ'
# '💩'
# ---
# ' '
# 'α'
# 'あ'
# '💩'
# ---
#  αあ💩
# αあ💩
# あ💩
# 💩
# ---
# ""
# ""
