trait ExprExts[t]:
    type VarExtRecRow
    type AppExtRecRow
    type AbsExtRecRow
    type LetExtRecRow

    defaultVarExt() (..VarExtRecRow)
    defaultAppExt() (..AppExtRecRow)
    defaultAbsExt() (..AbsExtRecRow)
    defaultLetExt() (..LetExtRecRow)

type Expr[exts]:
    Var(
        name: Str,
        ..ExprExts[exts].VarExtRecRow
    )

    App(
        fun: Expr[exts],
        arg: Expr[exts],
        ..ExprExts[exts].AppExtRecRow
    )

    Abs(
        param: Str,
        body: Expr[exts],
        ..ExprExts[exts].AbsExtRecRow
    )

    Let(
        name: Str,
        rhs: Expr[exts],
        body: Expr[exts],
        ..ExprExts[exts].LetExtRecRow
    )

type FmtExprExts

impl ExprExts[FmtExprExts]:
    type VarExtRecRow = row()
    type AppExtRecRow = row()
    type AbsExtRecRow = row()
    type LetExtRecRow = row()

    defaultVarExt() (..VarExtRecRow): ()
    defaultAppExt() (..AppExtRecRow): ()
    defaultAbsExt() (..AbsExtRecRow): ()
    defaultLetExt() (..LetExtRecRow): ()

type Ty:
    Var(Str)
    Arrow(Ty, Ty)

impl ToStr[Ty]:
    toStr(self: Ty) Str:
        panic("")

type TcExprExts

impl ExprExts[TcExprExts]:
    type VarExtRecRow = row(inferredTy: Option[Ty])
    type AppExtRecRow = row(inferredTy: Option[Ty])
    type AbsExtRecRow = row(inferredTy: Option[Ty])
    type LetExtRecRow = row(inferredTy: Option[Ty])

    defaultVarExt() (..VarExtRecRow): (inferredTy = Option.None)
    defaultAppExt() (..AppExtRecRow): (inferredTy = Option.None)
    defaultAbsExt() (..AbsExtRecRow): (inferredTy = Option.None)
    defaultLetExt() (..LetExtRecRow): (inferredTy = Option.None)

makeAstGeneric[ExprExts[t]]() Expr[t]:
    Expr.Var(name = "hi", ..ExprExts[t].defaultVarExt())

printExt[
    ExprExts[t],
    TypeLevelListToStr[RowToList[ExprExts[t].VarExtRecRow].List],
    TypeLevelListToStr[RowToList[ExprExts[t].AppExtRecRow].List],
    TypeLevelListToStr[RowToList[ExprExts[t].AbsExtRecRow].List],
    TypeLevelListToStr[RowToList[ExprExts[t].LetExtRecRow].List],
](expr: Expr[t]):
    match expr:
        Expr.Var(name, ..ext):
            print(RowToList[ExprExts[t].VarExtRecRow].rowToList(ext).typeLevelListToStr())

        Expr.App(fun, arg, ..ext):
            print(RowToList[ExprExts[t].AppExtRecRow].rowToList(ext).typeLevelListToStr())

        Expr.Abs(param, body, ..ext):
            print(RowToList[ExprExts[t].AbsExtRecRow].rowToList(ext).typeLevelListToStr())

        Expr.Let(name, rhs, body, ..ext):
            print(RowToList[ExprExts[t].LetExtRecRow].rowToList(ext).typeLevelListToStr())

main():
    printExt(makeAstGeneric[FmtExprExts, []]())
    printExt(makeAstGeneric[TcExprExts, []]())

# expected stdout:
# []
# inferredTy = Option.None -> []
