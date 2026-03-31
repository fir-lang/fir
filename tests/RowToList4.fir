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

recordToList(record: (..r)) Option[RecRowToList[r].List]:
    RecRowToList[r].rowToList(record)

type VarExtsList[t] = RecRowToList[ExprExts[t].VarExt].List
type AppExtsList[t] = RecRowToList[ExprExts[t].AppExt].List
type AbsExtsList[t] = RecRowToList[ExprExts[t].AbsExt].List
type LetExtsList[t] = RecRowToList[ExprExts[t].LetExt].List

printExt[
    ExprExts[t],
    ToStr[VarExtsList[t]],
    ToStr[AppExtsList[t]],
    ToStr[AbsExtsList[t]],
    ToStr[LetExtsList[t]],
](expr: Expr[t]):
    match expr:
        Expr.Var(name, ..ext):
            print(recordToList(ext))

        Expr.App(fun, arg, ..ext):
            print(recordToList(ext))

        Expr.Abs(param, body, ..ext):
            print(recordToList(ext))

        Expr.Let(name, rhs, body, ..ext):
            print(recordToList(ext))

main():
    printExt(makeAstGeneric[FmtExprExts, []]())
    printExt(makeAstGeneric[TcExprExts, []]())

# expected stdout:
# Option.None
# Option.Some(inferredTy = Option.None)
