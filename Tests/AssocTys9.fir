trait ExprExts[t]:
    type VarExt
    type AppExt
    type AbsExt
    type LetExt

    defaultVarExt() ExprExts[t].VarExt
    defaultAppExt() ExprExts[t].AppExt
    defaultAbsExt() ExprExts[t].AbsExt
    defaultLetExt() ExprExts[t].LetExt

type Expr[exts]:
    Var(
        name: Str,
        ext: ExprExts[exts].VarExt,
    )

    App(
        fun: Expr[exts],
        arg: Expr[exts],
        ext: ExprExts[exts].AppExt,
    )

    Abs(
        param: Str,
        body: Expr[exts],
        ext: ExprExts[exts].AbsExt,
    )

    Let(
        name: Str,
        rhs: Expr[exts],
        body: Expr[exts],
        ext: ExprExts[exts].LetExt,
    )

type FmtExprExts

impl ExprExts[FmtExprExts]:
    type VarExt = ()
    type AppExt = ()
    type AbsExt = ()
    type LetExt = ()

    defaultVarExt() ExprExts[FmtExprExts].VarExt: ()
    defaultAppExt() ExprExts[FmtExprExts].AppExt: ()
    defaultAbsExt() ExprExts[FmtExprExts].AbsExt: ()
    defaultLetExt() ExprExts[FmtExprExts].LetExt: ()

type Ty:
    Var(Str)
    Arrow(Ty, Ty)

impl ToStr[Ty]:
    toStr(self: Ty) Str:
        panic("")

type TcExprExts

impl ExprExts[TcExprExts]:
    type VarExt = Option[Ty]
    type AppExt = Option[Ty]
    type AbsExt = Option[Ty]
    type LetExt = Option[Ty]

    defaultVarExt() ExprExts[TcExprExts].VarExt: Option.None
    defaultAppExt() ExprExts[TcExprExts].AppExt: Option.None
    defaultAbsExt() ExprExts[TcExprExts].AbsExt: Option.None
    defaultLetExt() ExprExts[TcExprExts].LetExt: Option.None

makeAstGeneric[ExprExts[t]]() Expr[t]:
    Expr.Var(name = "hi", ext = ExprExts[t].defaultVarExt())

printExt[
    ExprExts[t],
    ToStr[ExprExts[t].VarExt],
    ToStr[ExprExts[t].AppExt],
    ToStr[ExprExts[t].AbsExt],
    ToStr[ExprExts[t].LetExt],
](expr: Expr[t]):
    match expr:
        Expr.Var(ext, ..): print(ext)
        Expr.App(ext, ..): print(ext)
        Expr.Abs(ext, ..): print(ext)
        Expr.Let(ext, ..): print(ext)

main():
    printExt(makeAstGeneric[FmtExprExts, []]())
    printExt(makeAstGeneric[TcExprExts, []]())

# expected stdout:
# ()
# Option.None
