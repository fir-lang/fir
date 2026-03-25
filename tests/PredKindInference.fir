type Foo[recRow](
    record: (b: Bool, ..recRow)
)

foo[RecRow[r]](foo: Foo[r]):
    match foo.record:
        (b = Bool.True, ..):
            print("true")
        (b = Bool.False, ..):
            print("false")

main():
    foo(Foo(record = (b = Bool.True, msg = "hi")))

# expected stdout: true
