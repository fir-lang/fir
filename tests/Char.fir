main():
    printStr(('a' == 'a').toStr())
    printStr(('a' == 'b').toStr())
    match 'a':
        'b': panic("'a' == 'b'".toStr())
        'a': printStr("👍")
        _: panic("Unexpected character")

    printStr('👍'._codePoint.toStr())

    # We can't convert or push a Char to a Str, for now check the code point.
    printStr(Char.fromU32(u32(128077)).unwrap()._codePoint.toStr())

    printStr('a'.lenUtf8().toStr())
    printStr('é'.lenUtf8().toStr())
    printStr('你'.lenUtf8().toStr())
    printStr('😄'.lenUtf8().toStr())

    testIsAsciiUppercase('A')
    testIsAsciiUppercase('Z')
    testIsAsciiUppercase('b')

    testIsAsciiLowercase('a')
    testIsAsciiLowercase('z')
    testIsAsciiLowercase('A')

    testIsAsciiDigit('0')
    testIsAsciiDigit('9')
    testIsAsciiDigit('b')

    testIsAsciiAlphanumeric('[')
    testIsAsciiAlphanumeric('a')

testIsAsciiUppercase(c: Char):
    printStr("`c`.isAsciiUppercase() = `c.isAsciiUppercase()`")

testIsAsciiLowercase(c: Char):
    printStr("`c`.isAsciiLowercase() = `c.isAsciiLowercase()`")

testIsAsciiDigit(c: Char):
    printStr("`c`.isAsciiDigit() = `c.isAsciiDigit()`")

testIsAsciiAlphanumeric(c: Char):
    printStr("`c`.isAsciiAlphanumeric() = `c.isAsciiAlphanumeric()`")

# expected stdout:
# Bool.True
# Bool.False
# 👍
# 128077
# 128077
# 1
# 2
# 3
# 4
# 'A'.isAsciiUppercase() = Bool.True
# 'Z'.isAsciiUppercase() = Bool.True
# 'b'.isAsciiUppercase() = Bool.False
# 'a'.isAsciiLowercase() = Bool.True
# 'z'.isAsciiLowercase() = Bool.True
# 'A'.isAsciiLowercase() = Bool.False
# '0'.isAsciiDigit() = Bool.True
# '9'.isAsciiDigit() = Bool.True
# 'b'.isAsciiDigit() = Bool.False
# '['.isAsciiAlphanumeric() = Bool.False
# 'a'.isAsciiAlphanumeric() = Bool.True
