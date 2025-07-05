main():
    let bytes = Vec.[
        u8(0x09),       # '\t', horizontal tab
        u8(0x0A),       # '\n', new line
        u8(0x0C),       # form feed
        u8(0x0D),       # '\r', carriage return
        u8(0x20),       # ' ', space
    ]

    let str = Str.fromUtf8Vec(bytes)

    for c: Char in str.chars():
        print(c.isAsciiWhitespace())
