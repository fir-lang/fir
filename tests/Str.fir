fn main() =
    printStr("asdf".startsWith("a").toStr())
    printStr("asdf".startsWith("as").toStr())
    printStr("asdf".startsWith("asd").toStr())
    printStr("asdf".startsWith("asdf").toStr())
    printStr("asdf".startsWith("asdfg").toStr())

# expected stdout:
# Bool.True
# Bool.True
# Bool.True
# Bool.True
# Bool.False
