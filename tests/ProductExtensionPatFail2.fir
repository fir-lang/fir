type Foo[r](
    x: Bool,
    ..r
)

foo[RecRow[r]](rec: Foo[r]):
    match rec:
        Foo(x = Bool.True, ..):
            print("true")
