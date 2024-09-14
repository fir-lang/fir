fn main(input: Str) =
    printStr(('a' == 'a').toStr())
    printStr(('a' == 'b').toStr())
    match 'a':
        'b': panic("'a' == 'b'".toStrView())
        'a': printStr("👍")

    printStr('👍'.value.toStr())

    # We can't convert or push a Char to a Str, for now check the value.
    printStr(Char.fromU32(128077u32).unwrap().value.toStr())

# expected stdout:
# Bool.True
# Bool.False
# 👍
# 128077
# 128077
