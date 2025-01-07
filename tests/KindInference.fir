# All `r` kinds below should be inferred as `row`.

type Test[r]:
    variant: [A, B, ..r]

fn f1[r](t: Test[r])
    match t.variant:
        `A: printStr("A")
        `B: printStr("B")
        other: printStr("Other")

fn f2[r](variant: [A, B, ..r])
    match variant:
        `A: printStr("A")
        `B: printStr("B")
        other: printStr("Other")

fn main()
    f1(Test(variant = `A))
    f1(Test(variant = `B))
    f1(Test(variant = `C))

    f2(`A)
    f2(`B)
    f2(`C)
