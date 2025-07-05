main():
    if Bool.False:
        u32(1)

    if Bool.False:
        u32(1)
    elif Bool.True:
        u32(2)

    match Bool.True:
        Bool.True: u32(123)

    match Bool.True:
        Bool.False: "Hi"
        Bool.True: u32(123)

    let x: U32 = if Bool.True:
        u32(1)
    else:
        u32(2)

    print(x)

    let y: U32 = match Bool.True:
        Bool.True: u32(1)
        Bool.False: u32(2)

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

StrBuilder.str(self, s: Str) StrBuilder:
    self._buf.pushStr(s)
    self

StrBuilder.char(self, c: Char) StrBuilder:
    self._buf.push(c)
    self

# expected stdout:
# 1
# 1
# OK
# 'x'

# expected stderr: tests/IfMatchStmtChecking.fir:10:5: Unexhaustive pattern match
