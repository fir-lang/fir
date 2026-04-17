main():
    let x: Option[U32].Foo = 1

# args: --typecheck
# expected exit status: 101
# expected stderr: Tests/Issue304.fir:2:12: Type Option is not a trait
