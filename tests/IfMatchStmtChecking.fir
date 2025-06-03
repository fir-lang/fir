main():
    if Bool.False:
        1u32

    if Bool.False:
        1u32
    elif Bool.True:
        2u32

    match Bool.True:
        Bool.True: 123u32

    match Bool.True:
        Bool.False: "Hi"
        Bool.True: 123u32

    let x: U32 = if Bool.True:
        1u32
    else:
        2u32

    print(x)

    let y: U32 = match Bool.True:
        Bool.True: 1u32
        Bool.False: 2u32

    print(y)

    # Examples from #112:
    let builder = StrBuilder(_buf = StrBuf.withCapacity(10))
    if Bool.False:
        builder.str("blah") 

    if Bool.False:
        builder.str("blah") 
    else:
        print("OK")

    # Example from the compiler code:
    let char = match "foo".chars().next():
        Option.Some(c):
            match c:
                'a': 'b'
                _: 'x'
        Option.None: 'x'

    print(char)

    ()

type StrBuilder:
    _buf: StrBuf

StrBuilder.str(self, s: Str) StrBuilder
    self._buf.pushStr(s)
    self

StrBuilder.char(self, c: Char) StrBuilder
    self._buf.push(c)
    self

# expected stdout:
# 1
# 1
# OK
# 'x'

# expected stderr: tests/IfMatchStmtChecking.fir:10:5: Unexhaustive pattern match
