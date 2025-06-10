type Test[varRowVar]:
    variant: [..varRowVar]

type Foo:
    Foo

main():
    let x: Test[[Foo]] = Test(variant = ~Foo.Foo)

# args: --typecheck --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/UnificationRowKindFail1.fir:8:26: Unable to unify var with kind row(variant) with type with kind *

