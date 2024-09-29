fn main() =
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
