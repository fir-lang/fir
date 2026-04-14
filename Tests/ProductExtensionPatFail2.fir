type Foo[recRow](
    x: Bool,
    ..recRow
)

main():
    let foo = Foo(x = Bool.True, msg = "hi")
    match foo:
        Foo(x = Bool.True):
            print("true")

# expected exit status: 101
# expected stderr:
# Tests/ProductExtensionPatFail2.fir:9:9: Unable to unify row() with row(msg: Str)
