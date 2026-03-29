type Foo[recRow](
    x: Bool,
    ..recRow
)

foo[r: Row[Rec]](rec: Foo[r]):
    match rec:
        Foo(x = Bool.True, ..):
            print("true")

# args: --typecheck
# expected stderr: tests/ProductExtensionPat3.fir:7:5: Unexhaustive pattern match
