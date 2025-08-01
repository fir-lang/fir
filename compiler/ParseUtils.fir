type ExprPrefix:
    Tilde
    Minus
    Not


type InlineExprCont:
    BinOp:
        op: BinOp
        rhs: Expr

    Is:
        pat: Pat


type ExprSuffix:
    Field:
        field: Id
        tyArgs: Vec[Type]

    Args:
        args: Vec[Named[Expr]]


parseCharLit(text: Str) Char:
    let chars = text.chars()

    let quote = chars.next().unwrap()

    # TODO: Make this an assertion
    if quote != '\'':
        panic("Bug in char lexer")

    let char = chars.next().unwrap()
    if char == '\\':
        match chars.next().unwrap():
            '\'': '\''
            'n': '\n'
            't': '\t'
            'r': '\r'
            '\\': '\\'
            other: panic("Unknown escaped character: '\\`other`'")
    else:
        char


parseStrParts(text: Str) Vec[StrPart]:
    Vec.empty() # TODO
