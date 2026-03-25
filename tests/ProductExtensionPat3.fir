type Foo[recRow](
    x: Bool,
    ..recRow
)

foo[RecRow[r]](rec: Foo[r]):
    match rec:
        Foo(x = Bool.True, ..):
            print("true")
