trait ExprExts[t]:
    type VarExt: Row[Rec]
    type AppExt: Row[Rec]
    type AbsExt: Row[Rec]
    type LetExt: Row[Rec]

    defaultVarExt() (..VarExt)
    defaultAppExt() (..AppExt)
    defaultAbsExt() (..AbsExt)
    defaultLetExt() (..LetExt)

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

    defaultVarExt() (..VarExt): ()
    defaultAppExt() (..AppExt): ()
    defaultAbsExt() (..AbsExt): ()
    defaultLetExt() (..LetExt): ()

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

    defaultVarExt() (..VarExt): (inferredTy = Option.None)
    defaultAppExt() (..AppExt): (inferredTy = Option.None)
    defaultAbsExt() (..AbsExt): (inferredTy = Option.None)
    defaultLetExt() (..LetExt): (inferredTy = Option.None)

makeAstGeneric[ExprExts[t]]() Expr[t]:
    Expr.Var(name = "hi", ..ExprExts[t].defaultVarExt())

printExt[
    ExprExts[t],
    ToStr[RecRowList[ExprExts[t].VarExt]],
    ToStr[RecRowList[ExprExts[t].AppExt]],
    ToStr[RecRowList[ExprExts[t].AbsExt]],
    ToStr[RecRowList[ExprExts[t].LetExt]],
](expr: Expr[t]):
    match expr:
        Expr.Var(name, ..ext):
            print(RecRowToList[ExprExts[t].VarExt].rowToList(ext))

        Expr.App(fun, arg, ..ext):
            print(RecRowToList[ExprExts[t].AppExt].rowToList(ext))

        Expr.Abs(param, body, ..ext):
            print(RecRowToList[ExprExts[t].AbsExt].rowToList(ext))

        Expr.Let(name, rhs, body, ..ext):
            print(RecRowToList[ExprExts[t].LetExt].rowToList(ext))

main():
    printExt(makeAstGeneric[FmtExprExts, []]())
    printExt(makeAstGeneric[TcExprExts, []]())

# expected stdout:
# Option.None
# Option.Some(inferredTy = Option.None)
