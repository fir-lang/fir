type Test[varRowVar]:
    variant: [..varRowVar]

main()
    let x: Test[[Foo]] = Test(variant = ~Foo)

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/UnificationRowKindFail1.fir:5:26: Unable to unify var with kind row(variant) with type with kind *
