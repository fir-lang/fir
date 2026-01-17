type Foo:
    A
    B


x() Foo:
    Foo.A


main():
    match x():
        Foo: ()

# expected exit status: 101
# expected stderr:
# tests/PatConFail4.fir:12:9: Type Foo is a sum type, the pattern needs a constructor
