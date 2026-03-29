type Foo[extras: Row[Rec]](
    x: U32,
    ..extras
)

main():
    let foo = Foo(x = 1, msg = "hi")
    match foo:
        Foo(msg = "hi", ..):
            print("true")

    foo.msg = "bye"
    match foo:
        Foo(msg = "hi", ..):
            print("true")
        Foo(msg = other, ..):
            print("other")

# expected stdout:
# true
# other

# expected stderr: tests/ProductExtensionPat2.fir:8:5: Unexhaustive pattern match
