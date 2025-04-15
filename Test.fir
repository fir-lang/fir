type Test[varRowErrs]:
    errs: [..varRowErrs]

main
    let x: Test[row[Foo]] = Test(errs = ~Foo)
    ()
