type Foo[extras](
    x: Bool,
    ..extras
)

main():
    let foo = Foo(x = Bool.True, msg = "hi")
    match foo:
        Foo(x = Bool.True):
            print("true")

# expected stdout:
# true
