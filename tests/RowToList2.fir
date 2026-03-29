trait ExprExts[t]:
    type VarExt
    type AppExt
    type AbsExt
    type LetExt

    defaultVarExt() VarExt
    defaultAppExt() AppExt
    defaultAbsExt() AbsExt
    defaultLetExt() LetExt

type Expr[exts]:
    Var(
        name: Str,
        ..RecordToRow[ExprExts[exts].VarExt].RecRow
    )

    App(
        fun: Expr[exts],
        arg: Expr[exts],
        ..RecordToRow[ExprExts[exts].AppExt].RecRow
    )

    Abs(
        param: Str,
        body: Expr[exts],
        ext: ExprExts[exts].AbsExt,
        ..RecordToRow[ExprExts[exts].AbsExt].RecRow
    )

    Let(
        name: Str,
        rhs: Expr[exts],
        body: Expr[exts],
        ..RecordToRow[ExprExts[exts].LetExt].RecRow
    )

type FmtExprExts

impl ExprExts[FmtExprExts]:
    type VarExt = ()
    type AppExt = ()
    type AbsExt = ()
    type LetExt = ()

    defaultVarExt() VarExt: ()
    defaultAppExt() AppExt: ()
    defaultAbsExt() AbsExt: ()
    defaultLetExt() LetExt: ()

type Ty:
    Var(Str)
    Arrow(Ty, Ty)

impl ToStr[Ty]:
    toStr(self: Ty) Str:
        panic("")

type TcExprExts

impl ExprExts[TcExprExts]:
    type VarExt = (inferredTy: Option[Ty])
    type AppExt = (inferredTy: Option[Ty])
    type AbsExt = (inferredTy: Option[Ty])
    type LetExt = (inferredTy: Option[Ty])

    defaultVarExt() VarExt: (inferredTy = Option.None)
    defaultAppExt() AppExt: (inferredTy = Option.None)
    defaultAbsExt() AbsExt: (inferredTy = Option.None)
    defaultLetExt() LetExt: (inferredTy = Option.None)

makeAstGeneric[ExprExts[t]]() Expr[t]:
    Expr.Var(name = "hi", ..ExprExts[t].defaultVarExt())

# args: --typecheck
