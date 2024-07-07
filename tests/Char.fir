fn main(input: Str) =
    printStr(('a' == 'a').toStr())
    printStr(('a' == 'b').toStr())
    match 'a':
        'b': panic("'a' == 'b'")
        'a': printStr("👍")

# expected stdout:
# Bool.True
# Bool.False
# 👍
