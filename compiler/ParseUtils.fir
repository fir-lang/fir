import Compiler.Ast


type ExprPrefix:
    Tilde(TokenIdx)
    Minus(TokenIdx)
    Not(TokenIdx)


type InlineExprCont:
    BinOp(op: BinOp, rhs: Expr)
    Is(pat: Pat)


type ExprSuffix:
    Field(field: Id, tyArgs: Option[TyArgs])
    Args(args: Vec[Named[Expr]], _lastToken: TokenIdx)


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


newId(cursor: U32) Id:
    Id(token = TokenIdx(idx = cursor))


processFields(fields: Vec[(name: Option[Id], ty: Type)]) ConFields:
    if fields.isEmpty():
        return ConFields.Empty

    let foundNamed = Bool.False
    let foundUnnamed = Bool.False

    for field: (name: Option[Id], ty: Type) in fields.iter():
        if field.name.isSome():
            foundNamed = Bool.True
        else:
            foundUnnamed = Bool.True

    if foundNamed and foundUnnamed:
        panic("Field list cannot have both named and unnamed fields")

    if foundNamed:
        let fs: Vec[(name: Id, ty: Type)] =
            fields.iter().map(|f: (name: Option[Id], ty: Type)|: (name = f.name.unwrap(), ty = f.ty)).toVec()
        ConFields.Named(fs)
    else:
        let fs: Vec[Type] =
            fields.iter().map(|f: (name: Option[Id], ty: Type)|: f.ty).toVec()
        ConFields.Unnamed(fs)
