# Same as `AssocTys9.fir`, but uses row types for associated types, and splices
# them in the `Expr` type consturctors.

trait ExprExts[t]:
    type VarExt
    type AppExt
    type AbsExt
    type LetExt

type Expr[exts]:
    Var(
        name: Str,
        ..ExprExts[exts].VarExt
    )

    App(
        fun: Expr[exts],
        arg: Expr[exts],
        ..ExprExts[exts].AppExt
    )

    Abs(
        param: Str,
        body: Expr[exts],
        ..ExprExts[exts].AbsExt
    )

    Let(
        name: Str,
        rhs: Expr[exts],
        body: Expr[exts],
        ..ExprExts[exts].LetExt
    )

type FmtExprExts

impl ExprExts[FmtExprExts]:
    type VarExt = row()
    type AppExt = row()
    type AbsExt = row()
    type LetExt = row()

type Ty:
    Var(Str)
    Arrow(Ty, Ty)

impl ToStr[Ty]:
    toStr(self: Ty) Str:
        panic("")

type TcExprExts

impl ExprExts[TcExprExts]:
    type VarExt = row(inferredTy: Option[Ty])
    type AppExt = row(inferredTy: Option[Ty])
    type AbsExt = row(inferredTy: Option[Ty])
    type LetExt = row(inferredTy: Option[Ty])

main():
    let tcExpr: Expr[TcExprExts] = Expr.Var(name = "hi", inferredTy = Option.None)
    let fmtExpr: Expr[FmtExprExts] = Expr.Var(name = "hi")
