type Foo[r] = (x: I32, ..r)

main():
    let x: Foo[U32] = (x = 1)

# expected exit status: 101
# expected stderr:
# Tests/TypeSynonymParamsFailKind.fir:4:23: Unable to unify types row() and U32 (kind mismatch, Row[Rec] ~ *)
