import Compiler.Ast


type ExprPrefix:
    Tilde(TokenIdx)
    Minus(TokenIdx)
    Not(TokenIdx)


type InlineExprCont:
    BinOp(
        op: BinOp,
        rhs: Expr,
    )
    Is(
        pat: Pat,
    )


type ExprSuffix:
    Field(
        field: Id,
        tyArgs: Option[TyArgs],
    )
    Args(
        args: Vec[Named[Expr]],
        _lastToken: TokenIdx,
    )


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
        let fs: Vec[(name: Id, ty: Type)] = fields.iter().map(
            |f: (name: Option[Id], ty: Type)|:
                (name = f.name.unwrap(), ty = f.ty),
        ).toVec()
        ConFields.Named(fs)
    else:
        let fs: Vec[Type] = fields.iter().map(
            |f: (name: Option[Id], ty: Type)|: f.ty,
        ).toVec()
        ConFields.Unnamed(fs)


# ------------------------------------------------------------------------------


associate(left: Expr, nodes: Vec[InlineExprCont]) Expr:
    if nodes.isEmpty():
        return left

    # Split the sequence into `and` or `or` -connected parts. Mixing `and` and `or` in a sequence is
    # a parse error (needs parens). Otherwise left associate.
    #
    # `makeLeftAssoc` will stop after handling an `is`. If there are unhandled continuations after
    # `makeLeftAssoc`, that means we have something like `expr1 is Pat + expr2`, which is also a
    # parse error.
    #
    # In other words, `foo is Pattern` can only be followed by an `and` or `or`. Anything else is a
    # parse error.

    let parts: Vec[(left: Expr, conts: Vec[InlineExprCont])] = Vec.empty()
    let foundAnd = Bool.False
    let foundOr = Bool.False

    let currentLeft = left
    let currentConts = Vec.empty()
    for node: InlineExprCont in nodes.iter():
        if node is InlineExprCont.BinOp(op, rhs) and op is BinOp.And | BinOp.Or:
            foundOr = foundOr or op is BinOp.Or
            foundAnd = foundAnd or op is BinOp.And
            parts.push((left = currentLeft, conts = currentConts))
            currentConts = Vec.empty()
            currentLeft = rhs
        else:
            currentConts.push(node)

    parts.push((left = currentLeft, conts = currentConts))

    if foundOr and foundAnd:
        panic("Binary expression with both 'and' and 'or'")

    let op = if foundOr:
        BinOp.Or
    else:
        BinOp.And

    let first = Bool.True
    let ret: Option[Expr] = Option.None
    for part: (left: Expr, conts: Vec[InlineExprCont]) in parts.iter():
        let partLeft = part.left
        let partConts = part.conts
        let expr = if partConts.isEmpty():
            partLeft
        else:
            match partConts.remove(0):
                InlineExprCont.Is(pat):
                    assert(partConts.isEmpty())
                    Expr.Is(IsExpr(expr = partLeft, pat = pat))
                InlineExprCont.BinOp(op, rhs):
                    let leftAssoc = makeLeftAssoc(
                        partLeft,
                        op,
                        rhs,
                        0,
                        partConts,
                        Option.None,
                    )
                    if leftAssoc.newIdx != partConts.len():
                        panic("Parse error")
                    leftAssoc.expr

        ret = match ret:
            Option.None: Option.Some(expr)
            Option.Some(ret_):
                Option.Some(Expr.BinOp(BinOpExpr(left = ret_, right = expr, op)))

    ret.unwrap()


makeLeftAssoc(
    left: Expr,
    op: BinOp,
    right: Expr,
    nextNodeIdx: U32,
    nodes: Vec[InlineExprCont],
    prec: Option[BinOp],
) (expr: Expr, newIdx: U32):
    loop:
        if nextNodeIdx == nodes.len():
            return (
                expr = Expr.BinOp(BinOpExpr(left, right, op)),
                newIdx = nextNodeIdx,
            )

        let nextNode = nodes.get(nextNodeIdx)

        let nextOpThings = match nextNode:
            InlineExprCont.Is(pat):
                return (
                    expr =
                        Expr.Is(
                            IsExpr(
                                expr = Expr.BinOp(BinOpExpr(left, right, op)),
                                pat,
                            ),
                        ),
                    newIdx = nextNodeIdx + 1,
                )
            InlineExprCont.BinOp(op = nextOp, rhs = nextRhs):
                (op = nextOp, rhs = nextRhs)

        let nextOp = nextOpThings.op
        let nextExpr = nextOpThings.rhs

        match assoc(op, nextOp):
            Assoc.Left:
                left = Expr.BinOp(
                    BinOpExpr(left = left, right = right, op = op,),
                )
                if prec is Option.Some(prec)
                        and assoc(prec, nextOp) is Assoc.Left | Assoc.Fail:
                    return (expr = left, newIdx = nextNodeIdx)
                op = nextOp
                right = nextExpr
                nextNodeIdx += 1

            Assoc.Right:
                let scanResult = makeLeftAssoc(
                    right,
                    nextOp,
                    nextExpr,
                    nextNodeIdx + 1,
                    nodes,
                    Option.Some(nextOp),
                )
                right = scanResult.expr
                nextNodeIdx = scanResult.newIdx

            Assoc.Fail: panic("Binary operator can't be associated")

    panic("unreachable")


type Assoc:
    ## The current expression should be on the left-hand side of the next operator.
    ##
    ## I.e. the next operator binds less tightly.
    Left

    ## The right-hand side expression of the current binop should be left-hand side of the next.
    ##
    ## I.e. the next operator binds more tightly.
    Right

    ## Fail means parens needed.
    Fail


assoc(left: BinOp, right: BinOp) Assoc:
    match left:
        BinOp.Multiply | BinOp.Divide:
            # `*` and `/` don't commute with bitwise operators, and bind more tightly than other
            # operators.
            if right
                    is BinOp.BitAnd
                        | BinOp.BitOr
                        | BinOp.LeftShift
                        | BinOp.RightShift:
                return Assoc.Fail

            Assoc.Left

        BinOp.Add | BinOp.Subtract:
            # `+` and `-` don't commute with bitwise operators, bind more tightly than relational
            # and logical operators, and less tightly than '*' and '/'.
            if right is BinOp.Add | BinOp.Subtract:
                return Assoc.Left

            if right is BinOp.Multiply | BinOp.Divide:
                return Assoc.Right

            if right
                    is BinOp.Equal
                        | BinOp.Gt
                        | BinOp.GtEq
                        | BinOp.Lt
                        | BinOp.LtEq
                        | BinOp.NotEqual
                        | BinOp.And
                        | BinOp.Or:
                return Assoc.Left

            Assoc.Fail

        BinOp.BitAnd:
            # `&&` only commutes with itself, and binds more tightly with relational and logical
            # operators.
            if right is BinOp.BitAnd:
                return Assoc.Left

            if right
                    is BinOp.Equal
                        | BinOp.Gt
                        | BinOp.GtEq
                        | BinOp.Lt
                        | BinOp.LtEq
                        | BinOp.NotEqual
                        | BinOp.And
                        | BinOp.Or:
                return Assoc.Left

            Assoc.Fail

        BinOp.BitOr:
            # Same as `&&`, but commutes with itself.
            if right is BinOp.BitOr:
                return Assoc.Left

            if right
                    is BinOp.Equal
                        | BinOp.Gt
                        | BinOp.GtEq
                        | BinOp.Lt
                        | BinOp.LtEq
                        | BinOp.NotEqual
                        | BinOp.And
                        | BinOp.Or:
                return Assoc.Left

            Assoc.Fail

        BinOp.LeftShift | BinOp.RightShift:
            # `<<` and `>>` don't commute, and bind more tightly than relational and binary
            # operators.
            if right
                    is BinOp.Equal
                        | BinOp.Gt
                        | BinOp.GtEq
                        | BinOp.Lt
                        | BinOp.LtEq
                        | BinOp.NotEqual
                        | BinOp.And
                        | BinOp.Or:
                return Assoc.Left

            Assoc.Fail

        BinOp.Equal
            | BinOp.Gt
            | BinOp.GtEq
            | BinOp.Lt
            | BinOp.LtEq
            | BinOp.NotEqual:
            # Relational operators don't commute. They bind less tightly than bitwise and arithmetic
            # operators, and more tightly than logical operators.
            if right
                    is BinOp.Multiply
                        | BinOp.Divide
                        | BinOp.Add
                        | BinOp.Subtract
                        | BinOp.LeftShift
                        | BinOp.RightShift
                        | BinOp.BitAnd
                        | BinOp.BitOr:
                return Assoc.Right

            if right is BinOp.And | BinOp.Or:
                return Assoc.Left

            Assoc.Fail

        BinOp.And:
            # `and` only commutes with itself, and binds less tightly than anything else.
            if right is BinOp.Or:
                return Assoc.Fail

            if right is BinOp.And:
                return Assoc.Left

            Assoc.Right

        BinOp.Or:
            # Similar to `and`.
            if right is BinOp.And:
                return Assoc.Fail

            if right is BinOp.Or:
                return Assoc.Left

            Assoc.Right
