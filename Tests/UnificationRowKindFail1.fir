type Test[row](
    variant: [..row],
)

type Foo:
    Foo

main():
    let x: Test[[Foo]] = Test(variant = ~Foo.Foo)

# args: --typecheck
# expected exit status: 101
# expected stderr:
# Tests/UnificationRowKindFail1.fir:9:26: Unable to unify types _0 and [Foo] (kind mismatch, Row[Var] ~ *)
