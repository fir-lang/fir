trait Exts[t]:
    type VarExt

type FmtExts

impl Exts[FmtExts]:
    type VarExt = ()

type Expr[exts]:
    Var(ext: Exts[exts].VarExt)

# Use Expr with a concrete ext type in a function that takes it as a parameter.
printVar(expr: Expr[FmtExts]):
    match expr:
        Expr.Var(ext):
            print(ext)

main():
    printVar(Expr.Var[FmtExts](ext = ()))

# expected stdout:
# ()
