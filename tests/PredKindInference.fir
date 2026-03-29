type Foo[recRow: Row[Rec]](
    record: (b: Bool, ..recRow)
)

foo[r: Row[Rec]](foo: Foo[r]):
    match foo.record:
        (b = Bool.True, ..):
            print("true")
        (b = Bool.False, ..):
            print("false")

main():
    foo(Foo(record = (b = Bool.True, msg = "hi")))

# expected stdout: true
