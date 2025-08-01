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
