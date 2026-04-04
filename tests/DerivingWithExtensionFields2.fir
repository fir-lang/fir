#[derive(ToDoc, Eq)]
type Foo[r: Row[Rec]]:
    A(A[r])
    B(B[r])


#[derive(ToDoc, Eq)]
type A[r](
    ..r
)


#[derive(ToDoc, Eq)]
type B[r](
    ..r
)

# args: --typecheck
