import [Compiler/Ast]


strParts(interpolations: Vec[(begin: Token, expr: Expr)]) Vec[StrPart]:
    let parts: Vec[StrPart] = Vec.withCapacity(interpolations.len() * 2)

    for part: (begin: Token, expr: Expr) in interpolations.iter():
        # Drop the `
        let str = part.begin.text
        let str = str.substr(0, str.len() - 1)
        parts.push(StrPart.Str(str))
        parts.push(StrPart.Expr(part.expr))

    parts


copyUpdateEscapes(s: Str) Str / exn:
    let ret = StrBuf.withCapacity(s.len())
    let chars: Peekable[CharIter, Char, exn] = s.chars().peekable()

    while chars.next[Peekable[CharIter, Char, exn], Char, exn]() is Option.Some(char):
        if char == '\\':
            # Escape sequences are recognized by the lexer, so we know '\\' is
            # followed by one of the characters below.
            match chars.next().unwrap():
                '\\': ret.push('\\')
                'n': ret.push('\n')
                't': ret.push('\t')
                'r': ret.push('\r')
                '"': ret.push('"')
                '`': ret.push('`')
                '\n':
                    while chars.peek[CharIter, Char, exn]() is Option.Some(next):
                        match next:
                            ' ' | '\t' | '\n' | '\r':
                                chars.next[Peekable[CharIter, Char, exn], Char, exn]()
                            _:
                                break
                other: panic("Weird escape character: `other.asU32()`")
        else:
            ret.push(char)

    ret.toStr()
