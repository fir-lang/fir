# Same as `AssocTys9.fir`, but uses type synonyms of associated types.

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
    type VarExt = Option[Ty]
    type AppExt = Option[Ty]
    type AbsExt = Option[Ty]
    type LetExt = Option[Ty]

    defaultVarExt() VarExt: Option.None
    defaultAppExt() AppExt: Option.None
    defaultAbsExt() AbsExt: Option.None
    defaultLetExt() LetExt: Option.None

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
