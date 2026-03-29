trait Foo[t]:
    type RecRow: Row[Rec]
    type VarRow: Row[Var]
    type Other

impl Foo[U32]:
    type RecRow = row()
    type VarRow = row[]
    type Other = U64

# args: --typecheck
