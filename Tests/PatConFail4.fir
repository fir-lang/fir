type Foo:
    A
    B


x() Foo:
    Foo.A


main():
    match x():
        Foo: ()

# expected exit status: 101
# expected stderr: Tests/PatConFail4.fir:12:9: Sum type allocation Foo needs a constructor
